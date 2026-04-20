#!/usr/bin/env python3
"""
Charleston County, SC — Motivated Seller Lead Scraper
======================================================

Data source: Register of Deeds (ROD) — the OFFICIAL Charleston County
government system for property-related recordings.

  ROD Day Book (today's filings):  https://roddaybook.charlestoncounty.org/
  ROD DM search (Deeds/Misc/LP):   https://www.charlestoncounty.gov/departments/rod/ds-DMTypeAndDate.php
  ROD FL search (Tax/Fed Liens):   https://www.charlestoncounty.gov/departments/rod/ds-FLTypeandDate.php
  Parcel enrichment (ArcGIS API):  https://gisccapps.charlestoncounty.org/arcgis/rest/services/
                                       GIS_VIEWER/Parcel_Search/MapServer/4/query

⚠️  LEGAL NOTICES — READ BEFORE RUNNING ⚠️
────────────────────────────────────────────
1. SC Code § 30-2-50(A) prohibits obtaining or using personal information
   from public records "for purposes of commercial solicitation directed to
   any person in the state of South Carolina." § 30-2-50(D) makes knowing
   violation a criminal misdemeanor. Consult an attorney before any direct-
   mail or phone campaign based on this data.

2. The SC Judicial Department Public Index (publicindex.sccourts.org)
   EXPLICITLY prohibits automated scraping. Therefore:
     • Court-filed JUDGMENTS (JUD/CCJ/DRJUD) are NOT collected here.
     • PROBATE COURT records are NOT collected here.
     • NOTICE OF FORECLOSURE filings (judicial foreclosure in SC) are NOT
       collected; LIS PENDENS filed in the ROD serves as the pre-foreclosure
       signal in South Carolina.
   These data types require manual lookup or a licensed data provider.

3. The county GIS data terms reiterate the same § 30-2-50 restrictions.

All records collected here are from the Register of Deeds (a county
recorder's office) and the county GIS REST API — both explicitly public.
────────────────────────────────────────────────────────────────────────

Architecture
────────────
  Source 1: ROD Day Book       → Playwright — all instrument types, today only
                                  Run daily and accumulate 7 days of records.
  Source 2: ROD DM Type+Date   → Playwright — LP, ML, NOC, Tax Deed, etc.
                                  7-day lookback; handles pagination.
  Source 3: ROD FL Type+Date   → Playwright — State / Federal / UCC liens
                                  7-day lookback.
  Enrichment: ArcGIS MapServer → requests JSON — owner name → site & mail addresses
                                  Charleston County Parcel layer (no bulk DBF exists).

Usage
─────
    python scraper/fetch.py [--lookback 7] [--headless 1] [--export-ghl]
"""

from __future__ import annotations

import argparse
import asyncio
import csv
import json
import logging
import os
import re
import sys
import time
import traceback
import unicodedata
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Optional
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup

try:
    from playwright.async_api import (
        async_playwright,
        TimeoutError as PWTimeout,
        Page,
    )
    HAS_PLAYWRIGHT = True
except ImportError:
    HAS_PLAYWRIGHT = False
    PWTimeout = Exception
    Page = Any

# ─────────────────────────────────────────────────────────────────────────────
# CONFIGURATION
# ─────────────────────────────────────────────────────────────────────────────

COUNTY  = "Charleston"
STATE   = "SC"

# ROD portals — all official charlestoncounty.gov URLs
ROD_DAYBOOK_URL      = "https://roddaybook.charlestoncounty.org/"
ROD_DM_TYPEDATE_URL  = ("https://www.charlestoncounty.gov/departments/rod/"
                         "ds-DMTypeAndDate.php")
ROD_FL_TYPEDATE_URL  = ("https://www.charlestoncounty.gov/departments/rod/"
                         "ds-FLTypeandDate.php")
ROD_DOC_VIEWER_BASE  = "https://docviewer.charlestoncounty.org/"

# ArcGIS parcel REST endpoint
# Layer 4 = Parcels in the Public_Search MapServer
ARCGIS_PARCEL_URL = (
    "https://gisccapps.charlestoncounty.org/arcgis/rest/services/"
    "GIS_VIEWER/Parcel_Search/MapServer/4/query"
)

LOOKBACK_DAYS   = int(os.environ.get("LOOKBACK_DAYS", "7"))
HEADLESS        = os.environ.get("HEADLESS", "1") != "0"

ROOT          = Path(__file__).resolve().parent.parent
DASHBOARD_DIR = ROOT / "dashboard"
DATA_DIR      = ROOT / "data"

DEFAULT_UA = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36 CHSLeadScraper/1.0"
)
HTTP_TIMEOUT   = 45
RETRY_ATTEMPTS = 3
RETRY_BACKOFF  = 4   # seconds; doubled per attempt

# ─────────────────────────────────────────────────────────────────────────────
# ROD INSTRUMENT TYPE CODES
# ─────────────────────────────────────────────────────────────────────────────
# Charleston County ROD uses short type codes in its DM search.
# Common codes discovered from the public portal; update `alt_codes` if the
# portal's dropdown/autocomplete reveals others.
#
# cat      = internal key for this scraper
# label    = human-readable label
# flag     = motivated-seller flag (None = informational only)
# rod_sec  = "DM" (Deeds/Misc) or "FL" (Liens/UCC) or "DAYBOOK"
# codes    = list of type strings to try in the Instrument Type field

DOC_SPECS: list[dict[str, Any]] = [
    # ── Deeds / Mortgages / Misc section ──────────────────────────────────
    {
        "cat": "LP",      "label": "Lis Pendens",
        "flag": "Lis pendens", "rod_sec": "DM",
        "codes": ["LP", "LIS PENDENS", "LIS PEN"],
    },
    {
        "cat": "RELLP",   "label": "Release of Lis Pendens",
        "flag": None,     "rod_sec": "DM",
        "codes": ["LPR", "LIS PEN REL", "REL LP", "RELLP"],
    },
    {
        "cat": "TAXDEED", "label": "Tax Deed",
        "flag": "Tax deed", "rod_sec": "DM",
        "codes": ["TD", "TAX DEED", "TAXD", "TAXDEED"],
    },
    {
        "cat": "NOC",     "label": "Notice of Commencement",
        "flag": None,     "rod_sec": "DM",
        "codes": ["NOC", "NOTICE OF COMMENCEMENT"],
    },
    {
        "cat": "LNMECH",  "label": "Mechanic's Lien",
        "flag": "Mechanic lien", "rod_sec": "DM",
        "codes": ["ML", "MECH", "MECHANIC", "MECH LIEN", "CLAIM OF LIEN"],
    },
    {
        "cat": "LNHOA",   "label": "HOA Lien",
        "flag": "HOA lien", "rod_sec": "DM",
        "codes": ["HOA", "HOA LIEN", "HOMEOWNERS"],
    },
    {
        "cat": "MEDLN",   "label": "Medicaid Lien",
        "flag": "Medicaid lien", "rod_sec": "DM",
        "codes": ["MED", "MEDICAID", "MED LIEN", "MEDLN"],
    },
    {
        "cat": "LN",      "label": "Lien",
        "flag": "Judgment lien", "rod_sec": "DM",
        "codes": ["LN", "LIEN"],
    },
    # ── Tax Liens / UCC section ───────────────────────────────────────────
    # The FL search uses a radio: State / Federal / UCC — not a code field.
    # We map each to a synthetic "cat" so scoring/flags work normally.
    {
        "cat": "LNIRS",    "label": "IRS / Federal Tax Lien",
        "flag": "Tax lien",  "rod_sec": "FL",
        "fl_type": "Federal",  # radio value on FL search
        "codes": ["IRST", "IRS", "FED LN", "FTL"],
    },
    {
        "cat": "LNFED",    "label": "Federal Lien",
        "flag": "Tax lien",  "rod_sec": "FL",
        "fl_type": "Federal",
        "codes": ["FEDL", "FEDERAL"],
    },
    {
        "cat": "LNCORPTX", "label": "State / Corp Tax Lien",
        "flag": "Tax lien",  "rod_sec": "FL",
        "fl_type": "State",
        "codes": ["STL", "STATE TAX", "CORP TAX"],
    },
    # ── Day Book only (all types via date range) ───────────────────────────
    # Collected automatically when we scrape the Day Book. The Day Book
    # returns the Inst code which we map back to the cats above.
]

# Quick reverse-lookup: inst code → DOC_SPEC  (built at startup)
_INST_TO_SPEC: dict[str, dict] = {}

# Entity keywords for flag detection
ENTITY_KW = (
    " LLC", " L.L.C", " INC", " CORP", " CORPORATION", " LTD",
    " LIMITED", " COMPANY", " CO ", " TRUST", " TR ", " ESTATE",
    " PROPERTIES", " HOLDINGS", " INVESTMENTS", " ASSOCIATION",
    " BANK", " LLLP", " PLLC", " FOUNDATION", " PARTNERSHIP",
)

# Scoring constants
SCORE_BASE        = 30
SCORE_PER_FLAG    = 10
SCORE_LP_FC_COMBO = 20
SCORE_AMT_100K    = 15
SCORE_AMT_50K     = 10
SCORE_NEW_WEEK    = 5
SCORE_HAS_ADDR    = 5

# ─────────────────────────────────────────────────────────────────────────────
# LOGGING
# ─────────────────────────────────────────────────────────────────────────────

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger("chs_leads")

# ─────────────────────────────────────────────────────────────────────────────
# DATA MODEL
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class Lead:
    doc_num:      str   = ""
    doc_type:     str   = ""
    filed:        str   = ""   # ISO date  YYYY-MM-DD
    cat:          str   = ""
    cat_label:    str   = ""
    owner:        str   = ""   # grantor / maker
    grantee:      str   = ""   # recipient
    amount:       float = 0.0
    legal:        str   = ""
    prop_address: str   = ""
    prop_city:    str   = ""
    prop_state:   str   = ""
    prop_zip:     str   = ""
    mail_address: str   = ""
    mail_city:    str   = ""
    mail_state:   str   = ""
    mail_zip:     str   = ""
    clerk_url:    str   = ""
    flags:        list[str] = field(default_factory=list)
    score:        int   = 0
    source:       str   = "ROD"

    def to_dict(self) -> dict:
        return asdict(self)

# ─────────────────────────────────────────────────────────────────────────────
# UTILITIES
# ─────────────────────────────────────────────────────────────────────────────

def normalize(s: Any) -> str:
    if not s:
        return ""
    s = unicodedata.normalize("NFKD", str(s))
    s = s.encode("ascii", "ignore").decode("ascii")
    return re.sub(r"\s+", " ", s).strip().upper()


def is_entity(name: str) -> bool:
    n = " " + normalize(name) + " "
    return any(kw in n for kw in ENTITY_KW)


def name_variants(full: str) -> list[str]:
    """Return 3 normalized name variants for parcel index lookups."""
    n = normalize(full)
    if not n:
        return []
    if is_entity(n):
        return [n]
    out = {n}
    if "," in n:
        last, rest = [x.strip() for x in n.split(",", 1)]
        out.add(f"{rest} {last}")
        out.add(f"{last} {rest}")
    else:
        parts = n.split()
        if len(parts) >= 2:
            first, *mid, last = parts
            mid_s = " ".join(mid)
            out.add(f"{last} {first} {mid_s}".strip())
            out.add(f"{last}, {first} {mid_s}".strip().rstrip(","))
    return list(out)


def parse_amount(s: Any) -> float:
    if s is None:
        return 0.0
    if isinstance(s, (int, float)):
        return float(s)
    m = re.search(r"\$?\s*([\d,]+(?:\.\d+)?)", str(s))
    if not m:
        return 0.0
    try:
        return float(m.group(1).replace(",", ""))
    except ValueError:
        return 0.0


def parse_date(s: Any) -> Optional[datetime]:
    if not s:
        return None
    if isinstance(s, datetime):
        return s
    txt = str(s).strip()
    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y",
                "%m/%d/%y", "%b %d, %Y", "%B %d, %Y"):
        try:
            return datetime.strptime(txt, fmt)
        except ValueError:
            continue
    return None


def iso(dt: Optional[datetime]) -> str:
    return dt.strftime("%Y-%m-%d") if dt else ""


def retry_sync(fn, label: str, attempts: int = RETRY_ATTEMPTS,
               backoff: float = RETRY_BACKOFF):
    """Call fn() with exponential backoff on failure."""
    delay = backoff
    last: Optional[BaseException] = None
    for i in range(1, attempts + 1):
        try:
            return fn()
        except Exception as exc:  # noqa: BLE001
            last = exc
            log.warning("[%s] attempt %d/%d failed: %s", label, i, attempts, exc)
            if i < attempts:
                time.sleep(delay)
                delay *= 2
    log.error("[%s] giving up after %d attempts", label, attempts)
    if last:
        raise last


async def aretry(label: str, coro_fn, *args,
                 attempts: int = RETRY_ATTEMPTS,
                 backoff: float = RETRY_BACKOFF, **kwargs):
    delay = backoff
    last: Optional[BaseException] = None
    for i in range(1, attempts + 1):
        try:
            return await coro_fn(*args, **kwargs)
        except Exception as exc:  # noqa: BLE001
            last = exc
            log.warning("[%s] async attempt %d/%d: %s", label, i, attempts, exc)
            if i < attempts:
                await asyncio.sleep(delay)
                delay *= 2
    log.error("[%s] giving up after %d attempts", label, attempts)
    if last:
        raise last

# ─────────────────────────────────────────────────────────────────────────────
# ROD DAY BOOK SCRAPER
# ─────────────────────────────────────────────────────────────────────────────

class DayBookScraper:
    """
    Scrapes roddaybook.charlestoncounty.org for all filings today.

    The Day Book search form (as of 2025-11-03) only exposes today's
    recordings. The form POSTs to the same page and the results are
    rendered as an HTML table.

    Columns returned:
      Record Date | Record Time | Maker Firm Name | Recipient Firm Name
      | Inst | Book-Page | Orig Book | Orig Page
    """

    def __init__(self, date_from: datetime, date_to: datetime,
                 headless: bool = True):
        self.date_from = date_from
        self.date_to   = date_to
        self.headless  = headless

    async def scrape(self) -> list[Lead]:
        if not HAS_PLAYWRIGHT:
            log.warning("Playwright not installed — skipping Day Book.")
            return []
        leads: list[Lead] = []
        async with async_playwright() as p:
            browser = await p.chromium.launch(headless=self.headless)
            ctx     = await browser.new_context(user_agent=DEFAULT_UA)
            page    = await ctx.new_page()
            page.set_default_timeout(30_000)
            try:
                leads = await aretry("daybook", self._run, page)
            except Exception as exc:  # noqa: BLE001
                log.error("Day Book failed: %s", exc)
            finally:
                await ctx.close()
                await browser.close()
        return leads

    async def _run(self, page: Page) -> list[Lead]:
        log.info("→ Day Book: %s", ROD_DAYBOOK_URL)
        await page.goto(ROD_DAYBOOK_URL, wait_until="domcontentloaded")

        # Fill in Begin / Thru dates
        begin_str = self.date_from.strftime("%m/%d/%Y 12:00 AM")
        thru_str  = self.date_to.strftime("%m/%d/%Y 11:59 PM")

        for sel, val in [
            ('input[id*="begin" i], input[name*="begin" i], '
             'input[placeholder*="Begin" i]', begin_str),
            ('input[id*="thru" i], input[name*="thru" i], '
             'input[placeholder*="Thru" i]',  thru_str),
        ]:
            loc = page.locator(sel).first
            try:
                if await loc.count() > 0:
                    await loc.fill("")
                    await loc.type(val, delay=30)
            except Exception:
                pass

        # Select "ALL" instrument types
        try:
            sel_loc = page.locator('select').first
            if await sel_loc.count() > 0:
                await sel_loc.select_option(label="ALL")
        except Exception:
            pass

        # Submit
        submit = page.locator('input[type="submit"], button[type="submit"]').first
        try:
            if await submit.count() > 0:
                await submit.click()
                await page.wait_for_load_state("networkidle", timeout=20_000)
        except (PWTimeout, Exception):
            pass

        return await self._parse_table(page)

    async def _parse_table(self, page: Page) -> list[Lead]:
        html  = await page.content()
        soup  = BeautifulSoup(html, "lxml")
        table = soup.find("table")
        if not table:
            return []

        rows = table.find_all("tr")
        if len(rows) < 2:
            return []

        headers = [normalize(th.get_text()) for th in rows[0].find_all(["th", "td"])]
        col = {h: i for i, h in enumerate(headers)}

        def g(cells: list, *keys: str) -> str:
            for k in keys:
                for h, i in col.items():
                    if k in h and i < len(cells):
                        return cells[i].get_text(" ", strip=True)
            return ""

        leads: list[Lead] = []
        for tr in rows[1:]:
            cells = tr.find_all("td")
            if not cells:
                continue
            try:
                inst_code = normalize(g(cells, "INST"))
                if not inst_code:
                    continue
                spec      = _inst_lookup(inst_code)
                if spec is None:
                    continue  # not a lead type we track

                rec_date  = g(cells, "RECORD DATE", "DATE")
                filed_dt  = parse_date(rec_date)

                # Link to document viewer
                link = ""
                a = tr.find("a", href=True)
                if a:
                    href = a["href"]
                    link = href if href.startswith("http") \
                           else urljoin(ROD_DOC_VIEWER_BASE, href)

                book_page = g(cells, "BOOK-PAGE", "BOOK", "PAGE")

                leads.append(Lead(
                    doc_num   = book_page.strip(),
                    doc_type  = inst_code,
                    filed     = iso(filed_dt),
                    cat       = spec["cat"],
                    cat_label = spec["label"],
                    owner     = normalize(g(cells, "MAKER")),
                    grantee   = normalize(g(cells, "RECIPIENT")),
                    clerk_url = link,
                    source    = "ROD-DayBook",
                ))
            except Exception as exc:  # noqa: BLE001
                log.debug("Day Book row error: %s", exc)
                continue
        log.info("  Day Book: %d leads from today", len(leads))
        return leads


def _build_inst_index() -> None:
    for spec in DOC_SPECS:
        for code in spec.get("codes", []):
            _INST_TO_SPEC[normalize(code)] = spec


def _inst_lookup(code: str) -> Optional[dict]:
    n = normalize(code)
    if n in _INST_TO_SPEC:
        return _INST_TO_SPEC[n]
    # Partial match
    for k, spec in _INST_TO_SPEC.items():
        if k in n or n in k:
            return spec
    return None


# ─────────────────────────────────────────────────────────────────────────────
# ROD DM TYPE + DATE SCRAPER  (Lis Pendens, Mechanic Lien, NOC, etc.)
# ─────────────────────────────────────────────────────────────────────────────

class RodDMScraper:
    """
    Searches the ROD Deeds/Mortgages/Misc "Type and Date" page
    for each DM instrument type in the lookback window.

    The form appears to be a PHP page that renders results in the same
    page (or loads them via JavaScript into a table). We use Playwright
    to fill + submit and then parse the resulting HTML table.
    """

    BASE_URL = ROD_DM_TYPEDATE_URL

    def __init__(self, date_from: datetime, date_to: datetime,
                 headless: bool = True):
        self.date_from = date_from
        self.date_to   = date_to
        self.headless  = headless
        self.specs     = [s for s in DOC_SPECS if s["rod_sec"] == "DM"]

    async def scrape(self) -> list[Lead]:
        if not HAS_PLAYWRIGHT:
            log.warning("Playwright not installed — skipping ROD DM scraper.")
            return []
        leads: list[Lead] = []
        async with async_playwright() as p:
            browser = await p.chromium.launch(headless=self.headless)
            ctx     = await browser.new_context(user_agent=DEFAULT_UA)
            page    = await ctx.new_page()
            page.set_default_timeout(30_000)
            try:
                for spec in self.specs:
                    try:
                        new = await aretry(
                            f"ROD-DM:{spec['cat']}",
                            self._scrape_one, page, spec,
                        )
                        if new:
                            log.info("  ROD-DM %s: %d record(s)",
                                     spec["cat"], len(new))
                            leads.extend(new)
                    except Exception as exc:  # noqa: BLE001
                        log.warning("ROD-DM %s failed: %s", spec["cat"], exc)
            finally:
                await ctx.close()
                await browser.close()
        return leads

    async def _scrape_one(self, page: Page, spec: dict) -> list[Lead]:
        await page.goto(self.BASE_URL, wait_until="domcontentloaded")

        date_from_str = self.date_from.strftime("%m/%d/%Y")
        date_to_str   = self.date_to.strftime("%m/%d/%Y")

        # ── Instrument Type field ─────────────────────────────────────────
        for code in spec["codes"]:
            filled = await self._try_fill_type(page, code)
            if filled:
                break

        # ── Date range fields ─────────────────────────────────────────────
        for from_sel, to_sel in [
            ('input[name*="Begin" i]',  'input[name*="Thru" i]'),
            ('input[name*="From" i]',   'input[name*="To" i]'),
            ('input[id*="Begin" i]',    'input[id*="Thru" i]'),
            ('input[id*="from" i]',     'input[id*="to" i]'),
        ]:
            f = page.locator(from_sel).first
            t = page.locator(to_sel).first
            try:
                if await f.count() > 0 and await t.count() > 0:
                    await f.fill(date_from_str)
                    await t.fill(date_to_str)
                    break
            except Exception:
                continue

        # ── Submit ────────────────────────────────────────────────────────
        submit = page.locator(
            'input[type="submit"], button[type="submit"], '
            'button:has-text("Search"), a:has-text("Search")'
        ).first
        try:
            if await submit.count() > 0:
                await submit.click()
                await page.wait_for_load_state("networkidle", timeout=25_000)
        except (PWTimeout, Exception):
            pass

        return await self._paginate(page, spec)

    async def _try_fill_type(self, page: Page, code: str) -> bool:
        """Try multiple selectors to fill the instrument type field."""
        selectors = [
            'input[name*="Type" i]:not([type="radio"]):not([type="checkbox"])',
            'input[id*="Type" i]:not([type="radio"]):not([type="checkbox"])',
            'input[name*="Instrument" i]',
            'input[placeholder*="Type" i]',
            'select[name*="Type" i]',
            'select[id*="Type" i]',
        ]
        for sel in selectors:
            loc = page.locator(sel).first
            try:
                if await loc.count() == 0:
                    continue
                tag = (await loc.evaluate("el => el.tagName")).upper()
                if tag == "SELECT":
                    # Try exact label, then partial
                    try:
                        await loc.select_option(label=code)
                        return True
                    except Exception:
                        pass
                    try:
                        opts = await loc.evaluate(
                            "el => [...el.options].map(o => o.text)")
                        match = next(
                            (o for o in opts
                             if code.upper() in o.upper()), None)
                        if match:
                            await loc.select_option(label=match)
                            return True
                    except Exception:
                        pass
                else:
                    await loc.fill("")
                    await loc.type(code, delay=25)
                    return True
            except Exception:
                continue
        return False

    async def _paginate(self, page: Page, spec: dict) -> list[Lead]:
        leads: list[Lead] = []
        for pg_num in range(1, 31):  # hard cap 30 pages
            batch = await self._parse_results(page, spec)
            leads.extend(batch)
            if not await self._next_page(page):
                break
        return leads

    async def _parse_results(self, page: Page, spec: dict) -> list[Lead]:
        html  = await page.content()
        soup  = BeautifulSoup(html, "lxml")
        table = _find_results_table(soup)
        if not table:
            return []

        header_cells = [normalize(th.get_text())
                        for th in table.find_all("th")]
        col = {h: i for i, h in enumerate(header_cells)}

        def g(cells: list, *keys: str) -> str:
            for k in keys:
                for h, i in col.items():
                    if k in h and i < len(cells):
                        return cells[i].get_text(" ", strip=True)
            return ""

        leads: list[Lead] = []
        for tr in table.find_all("tr"):
            cells = tr.find_all("td")
            if not cells:
                continue
            try:
                doc_num  = g(cells, "BOOK", "NEW BOOK", "DOC", "NUM", "PAGE")
                if not doc_num:
                    doc_num = cells[0].get_text(" ", strip=True)

                rec_date = g(cells, "RECORD DATE", "DATE", "FILED")
                filed_dt = parse_date(rec_date)

                # direct link
                link = ""
                for a in tr.find_all("a", href=True):
                    href = a["href"]
                    link = href if href.startswith("http") \
                           else urljoin(ROD_DOC_VIEWER_BASE, href)
                    break

                maker = normalize(g(cells, "MAKER", "GRANTOR", "DIRECT",
                                    "PARTY 1", "FROM"))
                recip = normalize(g(cells, "RECIPIENT", "GRANTEE",
                                    "INDIRECT", "PARTY 2", "TO"))
                amt   = parse_amount(g(cells, "AMOUNT", "CONSID", "VALUE"))

                if not maker and not doc_num:
                    continue

                leads.append(Lead(
                    doc_num   = doc_num.strip(),
                    doc_type  = spec["codes"][0],
                    filed     = iso(filed_dt),
                    cat       = spec["cat"],
                    cat_label = spec["label"],
                    owner     = maker,
                    grantee   = recip,
                    amount    = amt,
                    clerk_url = link,
                    source    = "ROD-DM",
                ))
            except Exception as exc:  # noqa: BLE001
                log.debug("ROD-DM row error: %s", exc)
                continue
        return leads

    async def _next_page(self, page: Page) -> bool:
        for sel in [
            'a:has-text("Next")', 'input[value="Next" i]',
            'button:has-text("Next")', 'a[id*="next" i]',
        ]:
            loc = page.locator(sel).first
            try:
                if await loc.count() == 0:
                    continue
                dis = await loc.get_attribute("disabled")
                if dis is not None:
                    return False
                cls = await loc.get_attribute("class") or ""
                if "disabled" in cls.lower():
                    return False
                await loc.click()
                try:
                    await page.wait_for_load_state("networkidle",
                                                   timeout=15_000)
                except PWTimeout:
                    pass
                return True
            except Exception:
                continue
        return False


def _find_results_table(soup: BeautifulSoup):
    """Find the best results table in the page HTML."""
    for t in soup.find_all("table"):
        headers = [normalize(th.get_text())
                   for th in t.find_all("th")]
        joined = " ".join(headers)
        if any(h in joined for h in
               ("MAKER", "BOOK", "RECORD DATE", "INST", "GRANTOR",
                "DOCUMENT", "DOC NUM", "PARTY")):
            return t
    return None


# ─────────────────────────────────────────────────────────────────────────────
# ROD FL (LIEN) SCRAPER  (IRS, Federal, State/Corp Tax Liens)
# ─────────────────────────────────────────────────────────────────────────────

class RodFLScraper:
    """
    Scrapes the ROD Tax Liens/UCC "Type and Date" page.

    The FL search uses a radio-button group (State / Federal / UCC / All)
    and a date range. Each run fetches one category.
    """

    BASE_URL = ROD_FL_TYPEDATE_URL

    def __init__(self, date_from: datetime, date_to: datetime,
                 headless: bool = True):
        self.date_from = date_from
        self.date_to   = date_to
        self.headless  = headless

    async def scrape(self) -> list[Lead]:
        if not HAS_PLAYWRIGHT:
            log.warning("Playwright not installed — skipping ROD FL scraper.")
            return []
        all_leads: list[Lead] = []
        # Deduplicate FL types so we don't request "Federal" twice
        seen_types: set[str] = set()
        fl_specs = [s for s in DOC_SPECS if s["rod_sec"] == "FL"]
        unique_types = []
        for spec in fl_specs:
            ft = spec.get("fl_type", "All")
            if ft not in seen_types:
                seen_types.add(ft)
                unique_types.append((ft, spec))

        async with async_playwright() as p:
            browser = await p.chromium.launch(headless=self.headless)
            ctx     = await browser.new_context(user_agent=DEFAULT_UA)
            page    = await ctx.new_page()
            page.set_default_timeout(30_000)
            try:
                for fl_type, spec in unique_types:
                    try:
                        new = await aretry(
                            f"ROD-FL:{fl_type}",
                            self._scrape_one, page, fl_type, spec,
                        )
                        if new:
                            log.info("  ROD-FL %s: %d record(s)",
                                     fl_type, len(new))
                            all_leads.extend(new)
                    except Exception as exc:  # noqa: BLE001
                        log.warning("ROD-FL %s failed: %s", fl_type, exc)
            finally:
                await ctx.close()
                await browser.close()
        return all_leads

    async def _scrape_one(self, page: Page,
                          fl_type: str, spec: dict) -> list[Lead]:
        await page.goto(self.BASE_URL, wait_until="domcontentloaded")

        date_from_str = self.date_from.strftime("%m/%d/%Y")
        date_to_str   = self.date_to.strftime("%m/%d/%Y")

        # Select lien type radio button (State / Federal / UCC / All)
        for sel in [
            f'input[type="radio"][value="{fl_type}" i]',
            f'input[type="radio"][id*="{fl_type}" i]',
            f'label:has-text("{fl_type}") input[type="radio"]',
        ]:
            loc = page.locator(sel).first
            try:
                if await loc.count() > 0:
                    await loc.check()
                    break
            except Exception:
                continue

        # Date range
        for from_sel, to_sel in [
            ('input[name*="Begin" i]', 'input[name*="Thru" i]'),
            ('input[name*="From" i]',  'input[name*="To" i]'),
            ('input[id*="begin" i]',   'input[id*="thru" i]'),
        ]:
            f = page.locator(from_sel).first
            t = page.locator(to_sel).first
            try:
                if await f.count() > 0 and await t.count() > 0:
                    await f.fill(date_from_str)
                    await t.fill(date_to_str)
                    break
            except Exception:
                continue

        # Submit
        submit = page.locator(
            'input[type="submit"], button[type="submit"], '
            'button:has-text("Search")'
        ).first
        try:
            if await submit.count() > 0:
                await submit.click()
                await page.wait_for_load_state("networkidle", timeout=25_000)
        except (PWTimeout, Exception):
            pass

        # Paginate
        leads: list[Lead] = []
        for _ in range(30):
            html  = await page.content()
            soup  = BeautifulSoup(html, "lxml")
            table = _find_results_table(soup)
            if not table:
                break
            for tr in table.find_all("tr"):
                cells = tr.find_all("td")
                if not cells:
                    continue
                try:
                    doc_num = cells[0].get_text(" ", strip=True)
                    if not doc_num:
                        continue
                    header_cells = [normalize(th.get_text())
                                    for th in table.find_all("th")]
                    col_map = {h: i for i, h in enumerate(header_cells)}

                    def g2(c: list, *keys: str) -> str:
                        for k in keys:
                            for h, i in col_map.items():
                                if k in h and i < len(c):
                                    return c[i].get_text(" ", strip=True)
                        return ""

                    rec_date = g2(cells, "DATE", "RECORD", "FILED")
                    filed_dt = parse_date(rec_date)

                    link = ""
                    a = tr.find("a", href=True)
                    if a:
                        href = a["href"]
                        link = href if href.startswith("http") \
                               else urljoin(ROD_DOC_VIEWER_BASE, href)

                    maker = normalize(g2(cells, "MAKER", "DEBTOR", "GRANTOR"))
                    recip = normalize(g2(cells, "RECIPIENT", "SECURED",
                                         "SECURED PARTY"))
                    leads.append(Lead(
                        doc_num   = doc_num.strip(),
                        doc_type  = fl_type,
                        filed     = iso(filed_dt),
                        cat       = spec["cat"],
                        cat_label = spec["label"],
                        owner     = maker,
                        grantee   = recip,
                        clerk_url = link,
                        source    = "ROD-FL",
                    ))
                except Exception:
                    continue

            # Next page
            found_next = False
            for sel in ['a:has-text("Next")', 'input[value="Next" i]']:
                loc = page.locator(sel).first
                try:
                    if await loc.count() > 0:
                        dis = await loc.get_attribute("disabled")
                        if dis is not None:
                            break
                        await loc.click()
                        await page.wait_for_load_state("networkidle",
                                                       timeout=15_000)
                        found_next = True
                        break
                except Exception:
                    continue
            if not found_next:
                break

        return leads


# ─────────────────────────────────────────────────────────────────────────────
# PARCEL ENRICHMENT — ArcGIS REST API
# ─────────────────────────────────────────────────────────────────────────────
# Charleston County does NOT offer a downloadable bulk DBF.
# Parcel data is served via the county's ArcGIS MapServer REST API.
#
# Endpoint:  ARCGIS_PARCEL_URL (MapServer layer 4)
# Strategy:  query by owner name (WHERE clause), return first match.
#            We cache all queries to avoid re-hitting for the same owner.
# ─────────────────────────────────────────────────────────────────────────────

_PARCEL_CACHE: dict[str, Optional[dict]] = {}

# We discover field names on first call
_PARCEL_FIELDS: list[str] = []

# Field name candidates — the actual names depend on the county's schema
_OWN_CANDS   = ["OWNER1", "OWNER", "OWN1", "OWN_NAME", "OWNERNAME",
                 "OWNER_NAME"]
_SITE_CANDS  = ["SITEADDR", "SITE_ADDR", "PHYSADDR", "ADDRESS",
                 "LOCATION", "PHY_ADDR1"]
_SCITY_CANDS = ["SITECITY", "SITE_CITY", "PHYCITY", "CITY"]
_SZIP_CANDS  = ["SITEZIP",  "SITE_ZIP",  "PHYZIP",  "ZIP"]
_MAIL_CANDS  = ["MAILADDR1","MAIL_ADDR", "MAILADR1", "MAILING",
                 "MAILINGADDR"]
_MCITY_CANDS = ["MAILCITY", "MAIL_CITY", "MAILCIT"]
_MSTATE_CANDS= ["MAILSTATE","MAIL_STATE","MAILST"]
_MZIP_CANDS  = ["MAILZIP",  "MAIL_ZIP",  "MAILZP"]


def _pick(attrs: dict, candidates: list[str]) -> str:
    au = {k.upper(): v for k, v in attrs.items()}
    for c in candidates:
        v = au.get(c.upper())
        if v not in (None, ""):
            return str(v).strip()
    return ""


def _get_parcel_fields() -> list[str]:
    """Fetch the field list from the layer endpoint (once)."""
    global _PARCEL_FIELDS
    if _PARCEL_FIELDS:
        return _PARCEL_FIELDS
    try:
        resp = requests.get(
            ARCGIS_PARCEL_URL.replace("/query", ""),
            params={"f": "json"}, timeout=HTTP_TIMEOUT,
            headers={"User-Agent": DEFAULT_UA},
        )
        resp.raise_for_status()
        data = resp.json()
        _PARCEL_FIELDS = [f["name"] for f in data.get("fields", [])]
        log.info("ArcGIS parcel fields discovered: %s",
                 ", ".join(_PARCEL_FIELDS[:8]) + "…")
    except Exception as exc:  # noqa: BLE001
        log.warning("Could not fetch ArcGIS field list: %s", exc)
        _PARCEL_FIELDS = []
    return _PARCEL_FIELDS


def _query_parcel(owner_name: str) -> Optional[dict]:
    """Return first matching parcel record for owner_name, or None."""
    key = normalize(owner_name)
    if key in _PARCEL_CACHE:
        return _PARCEL_CACHE[key]

    result = None
    for variant in name_variants(owner_name):
        if not variant:
            continue
        try:
            escaped = variant.replace("'", "''")
            candidates = _pick_owner_fields()
            where_parts = [f"UPPER({f}) = '{escaped}'"
                           for f in candidates] if candidates else \
                          ["1=1"]
            where = " OR ".join(where_parts)

            resp = requests.get(
                ARCGIS_PARCEL_URL,
                params={
                    "where":         where,
                    "outFields":     "*",
                    "returnGeometry":"false",
                    "resultRecordCount": 1,
                    "f":             "json",
                },
                timeout=HTTP_TIMEOUT,
                headers={"User-Agent": DEFAULT_UA},
            )
            resp.raise_for_status()
            data = resp.json()
            feats = data.get("features", [])
            if feats:
                result = feats[0].get("attributes", {})
                break
        except Exception as exc:  # noqa: BLE001
            log.debug("ArcGIS query error for '%s': %s", variant, exc)
            continue

    _PARCEL_CACHE[key] = result
    return result


def _pick_owner_fields() -> list[str]:
    """Return which owner field names actually exist in the layer."""
    known = _get_parcel_fields()
    if not known:
        return _OWN_CANDS  # fallback; API will return error if wrong
    ku = [f.upper() for f in known]
    return [c for c in _OWN_CANDS if c.upper() in ku]


def enrich_with_parcel(lead: Lead) -> None:
    """In-place address enrichment from ArcGIS parcel layer."""
    if not lead.owner:
        return
    try:
        rec = _query_parcel(lead.owner)
        if not rec:
            return
        lead.prop_address = lead.prop_address or _pick(rec, _SITE_CANDS)
        lead.prop_city    = lead.prop_city    or _pick(rec, _SCITY_CANDS)
        lead.prop_state   = lead.prop_state   or _pick(rec, ["STATE",
                                                               "SITE_STATE"])
        if not lead.prop_state:
            lead.prop_state = STATE
        lead.prop_zip     = lead.prop_zip     or _pick(rec, _SZIP_CANDS)
        lead.mail_address = lead.mail_address or _pick(rec, _MAIL_CANDS)
        lead.mail_city    = lead.mail_city    or _pick(rec, _MCITY_CANDS)
        lead.mail_state   = lead.mail_state   or _pick(rec, _MSTATE_CANDS)
        if not lead.mail_state:
            lead.mail_state = STATE
        lead.mail_zip     = lead.mail_zip     or _pick(rec, _MZIP_CANDS)
    except Exception as exc:  # noqa: BLE001
        log.debug("Parcel enrich failed for '%s': %s", lead.owner, exc)


# ─────────────────────────────────────────────────────────────────────────────
# SCORING + FLAGS
# ─────────────────────────────────────────────────────────────────────────────

def compute_flags(lead: Lead,
                  by_owner: dict[str, list[Lead]]) -> list[str]:
    flags: list[str] = []

    # Base flag from doc type
    for spec in DOC_SPECS:
        if spec["cat"] == lead.cat and spec.get("flag"):
            if spec["flag"] not in flags:
                flags.append(spec["flag"])
            break

    if is_entity(lead.owner):
        flags.append("LLC / corp owner")

    filed_dt = parse_date(lead.filed)
    if filed_dt and (datetime.now() - filed_dt).days <= 7:
        flags.append("New this week")

    # LP + FC/Tax-deed combo by same owner
    owner_key = normalize(lead.owner)
    if owner_key:
        same = by_owner.get(owner_key, [])
        cats = {l.cat for l in same}
        if "LP" in cats and ("TAXDEED" in cats or "LNIRS" in cats
                             or "LNCORPTX" in cats):
            flags.append("LP+FC combo")

    # Deduplicate
    seen, out = set(), []
    for f in flags:
        if f not in seen:
            out.append(f)
            seen.add(f)
    return out


def compute_score(lead: Lead) -> int:
    s = SCORE_BASE
    s += SCORE_PER_FLAG * len([f for f in lead.flags if f != "LP+FC combo"])
    if "LP+FC combo" in lead.flags:
        s += SCORE_LP_FC_COMBO
    if lead.amount > 100_000:
        s += SCORE_AMT_100K
    elif lead.amount > 50_000:
        s += SCORE_AMT_50K
    if "New this week" in lead.flags:
        s += SCORE_NEW_WEEK
    if lead.prop_address or lead.mail_address:
        s += SCORE_HAS_ADDR
    return max(0, min(100, s))


# ─────────────────────────────────────────────────────────────────────────────
# OUTPUT
# ─────────────────────────────────────────────────────────────────────────────

def write_records_json(leads: list[Lead],
                       date_from: datetime, date_to: datetime) -> None:
    with_addr = sum(1 for l in leads
                    if l.prop_address or l.mail_address)
    payload = {
        "fetched_at":   datetime.now(timezone.utc).isoformat(),
        "source":       f"{COUNTY} County, {STATE} — Register of Deeds + ArcGIS",
        "date_range":   {"from": iso(date_from), "to": iso(date_to)},
        "total":        len(leads),
        "with_address": with_addr,
        "records":      [l.to_dict() for l in leads],
    }
    for target in (DASHBOARD_DIR / "records.json",
                   DATA_DIR      / "records.json"):
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(
            json.dumps(payload, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        log.info("wrote %s (%d records)", target, len(leads))


def split_name(full: str) -> tuple[str, str]:
    n = str(full or "").strip()
    if not n:
        return "", ""
    if is_entity(n):
        return "", n
    if "," in n:
        last, first = [p.strip() for p in n.split(",", 1)]
        first = first.split()[0] if first else ""
        return first.title(), last.title()
    parts = n.split()
    if len(parts) == 1:
        return "", parts[0].title()
    return parts[0].title(), parts[-1].title()


def write_ghl_csv(leads: list[Lead]) -> Path:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / f"leads_ghl_{datetime.now():%Y%m%d}.csv"
    cols = [
        "First Name", "Last Name",
        "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
        "Property Address", "Property City", "Property State", "Property Zip",
        "Lead Type", "Document Type", "Date Filed",
        "Document Number", "Amount/Debt Owed",
        "Seller Score", "Motivated Seller Flags",
        "Source", "Public Records URL",
    ]
    with out.open("w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(cols)
        for l in leads:
            first, last = split_name(l.owner)
            w.writerow([
                first, last,
                l.mail_address, l.mail_city,
                l.mail_state or STATE, l.mail_zip,
                l.prop_address, l.prop_city,
                l.prop_state  or STATE, l.prop_zip,
                l.cat_label, l.doc_type, l.filed,
                l.doc_num,
                f"{l.amount:.2f}" if l.amount else "",
                l.score,
                "; ".join(l.flags),
                f"{COUNTY} County, {STATE} Register of Deeds",
                l.clerk_url,
            ])
    log.info("wrote %s", out)
    return out


# ─────────────────────────────────────────────────────────────────────────────
# DEDUP + PIPELINE
# ─────────────────────────────────────────────────────────────────────────────

def dedupe(leads: list[Lead]) -> list[Lead]:
    seen: set[str] = set()
    out: list[Lead] = []
    for l in leads:
        key = f"{normalize(l.doc_num)}|{l.cat}"
        if key in seen:
            continue
        seen.add(key)
        out.append(l)
    return out


async def run(args: argparse.Namespace) -> int:
    _build_inst_index()

    date_to   = datetime.now()
    date_from = date_to - timedelta(days=args.lookback)

    log.info("=" * 66)
    log.info("Charleston County, SC — Motivated Seller Lead Scraper")
    log.info("Lookback: %d days  (%s → %s)",
             args.lookback, iso(date_from), iso(date_to))
    log.info("ROD Day Book: %s", ROD_DAYBOOK_URL)
    log.info("ROD DM:       %s", ROD_DM_TYPEDATE_URL)
    log.info("ROD FL:       %s", ROD_FL_TYPEDATE_URL)
    log.info("ArcGIS:       %s", ARCGIS_PARCEL_URL)
    log.info("=" * 66)

    leads: list[Lead] = []

    # 1 ── Day Book (today's filings — all instrument types)
    try:
        log.info("[1/3] Day Book scrape…")
        db_leads = await DayBookScraper(
            date_from, date_to, headless=args.headless
        ).scrape()
        leads.extend(db_leads)
    except Exception as exc:  # noqa: BLE001
        log.error("Day Book scrape failed: %s", exc)

    # 2 ── ROD DM type+date (Lis Pendens, Mech Lien, NOC, Tax Deed, …)
    try:
        log.info("[2/3] ROD DM type+date scrape…")
        dm_leads = await RodDMScraper(
            date_from, date_to, headless=args.headless
        ).scrape()
        leads.extend(dm_leads)
    except Exception as exc:  # noqa: BLE001
        log.error("ROD DM scrape failed: %s", exc)

    # 3 ── ROD FL (State / Federal / UCC liens)
    try:
        log.info("[3/3] ROD FL tax/federal lien scrape…")
        fl_leads = await RodFLScraper(
            date_from, date_to, headless=args.headless
        ).scrape()
        leads.extend(fl_leads)
    except Exception as exc:  # noqa: BLE001
        log.error("ROD FL scrape failed: %s", exc)

    leads = dedupe(leads)
    log.info("Total unique ROD records: %d", len(leads))

    # ── Parcel enrichment via ArcGIS REST API ─────────────────────────────
    log.info("Enriching with parcel data (ArcGIS)…")
    _get_parcel_fields()  # pre-warm field cache
    enriched = 0
    for lead in leads:
        try:
            before = lead.prop_address
            enrich_with_parcel(lead)
            if lead.prop_address and not before:
                enriched += 1
        except Exception:
            pass
    log.info("  enriched %d lead(s) with parcel addresses", enriched)

    # ── Flags + scoring ───────────────────────────────────────────────────
    by_owner: dict[str, list[Lead]] = {}
    for l in leads:
        by_owner.setdefault(normalize(l.owner), []).append(l)
    for l in leads:
        l.flags = compute_flags(l, by_owner)
        l.score = compute_score(l)
    leads.sort(key=lambda x: -x.score)

    # ── Output ────────────────────────────────────────────────────────────
    write_records_json(leads, date_from, date_to)
    if args.export_ghl:
        write_ghl_csv(leads)

    with_addr = sum(1 for l in leads if l.prop_address or l.mail_address)
    log.info("DONE — %d leads total; %d with addresses.", len(leads), with_addr)
    log.info("")
    log.info("⚠  REMINDER: SC Code § 30-2-50 prohibits using this data for")
    log.info("   commercial solicitation. Consult an attorney before any")
    log.info("   direct-mail or cold-call campaign.")
    return 0


def cli() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lookback", type=int, default=LOOKBACK_DAYS,
                   help="Days to look back (default: 7)")
    p.add_argument("--headless", type=lambda x: x != "0",
                   default=HEADLESS,
                   help="Run Playwright headless (default: 1)")
    p.add_argument("--export-ghl", action="store_true",
                   help="Also write GoHighLevel CSV to data/")
    args = p.parse_args()
    try:
        return asyncio.run(run(args))
    except KeyboardInterrupt:
        log.warning("Interrupted.")
        return 130


if __name__ == "__main__":
    sys.exit(cli())
