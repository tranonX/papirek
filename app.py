#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Papírek – scraper akčních cen z Kupi.cz + malý lokální server pro aplikaci.

Spuštění:            python app.py
Zkouška scraperu:    python app.py hledej mléko
Rozbor uložené str.: python app.py soubor stranka.html

Nepotřebuje nic doinstalovat, stačí samotný Python 3.8 nebo novější.
"""
import datetime
import json
import os
import re
import sys
import socket
import ssl
import threading
import base64
import hmac
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from html.parser import HTMLParser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ---------------------------------------------------------------- NASTAVENÍ
ZAKLAD = "https://www.kupi.cz"
V_CLOUDU = bool(os.environ.get("PORT"))      # na serveru (Render apod.) port nastavuje hosting
PORT = int(os.environ.get("PORT", "8765"))  # doma bude adresa aplikace http://localhost:8765
HESLO = os.environ.get("PAPIREK_HESLO", "")  # na serveru: heslo, ať Papírek nepoužívá kdokoli
CACHE_HODIN = 6        # jak dlouho si pamatovat stažené ceny (šetří Kupi.cz i tvůj čas)
MAX_STRAN = 2          # kolik stránek výsledků stáhnout na jedno hledání
PAUZA = 1.0            # pauza mezi dotazy na Kupi.cz v sekundách
UA = "Papirek/1.0 (osobni nakupni seznam)"
OKOLI_KM = 10          # do jaké vzdálenosti hledat pobočky obchodů
OVERPASS = ["https://overpass-api.de/api/interpreter",
            "https://overpass.kumi.systems/api/interpreter"]   # mapová data OpenStreetMap
NOMINATIM = "https://nominatim.openstreetmap.org/search"       # převod adresy na souřadnice

VERZE = "2026-11-18a"
SLOZKA = os.path.dirname(os.path.abspath(__file__))
CACHE_SOUBOR = os.path.join(SLOZKA, "cache.json")
LADENI_SOUBOR = os.path.join(SLOZKA, "posledni_stranka.html")


# ---------------------------------------------------------------- POMOCNÉ FUNKCE
def cisti(text):
    """Odstraní pevné mezery a zbytečné bílé znaky."""
    return " ".join(text.replace("\xa0", " ").split())


def cislo(text):
    """'1 299,90' -> 1299.9"""
    try:
        return float(text.replace(" ", "").replace(",", "."))
    except ValueError:
        return None


def absolutni(href):
    return urllib.parse.urljoin(ZAKLAD + "/", href)


RE_CENA = re.compile(r"cena\s*(?:od\s*)?(\d[\d ]*(?:,\d{1,2})?)\s*Kč", re.I)
RE_CENA_NOUZE = re.compile(r"(\d[\d ]*,\d{2})\s*Kč")
RE_MNOZSTVI = re.compile(r"\s*/\s*((?:\d+\s*[x×]\s*)?\d+(?:[.,]\d+)?\s*[^\W\d_]+)")
RE_JEDNOTKA = re.compile(r"(\d[\d ]*,\d{2})\s*Kč\s*/\s*(\d+(?:[.,]\d+)?)\s*([^\W\d_]+)")
RE_SLEVA = re.compile(r"[–−-]\s*(\d{1,2})\s*%")
RE_DATUM = re.compile(r"(\d{1,2})\.\s*(\d{1,2})\.")
RE_KLUB = re.compile(r"členy klubu|cena s\s|kartou|card|věrnostní|mobilní aplikac", re.I)
RE_VELIKOST = re.compile(r"(?:\d+\s*[x×]\s*)?\d+(?:[.,]\d+)?\s*[^\W\d_]+")
RE_OBAL = [("plech", re.compile(r"\bplech", re.I)),
           ("pet", re.compile(r"\bpet\b", re.I)),
           ("sklo", re.compile(r"\bsklo\b|skleněn|\bl[aá]hev\b|vratn", re.I))]
RE_BEZNA = re.compile(r"Běžná cena:?\s*(\d[\d ]*,\d{2})\s*Kč", re.I)
RE_STOP = re.compile(r"^(od\b|akce dle ceny|doporučené akce|ilustrační)|Kč", re.I)


def datum_iso(den, mesic, dnes):
    """Z '17. 11.' udělá celé datum. Rok vybere tak, aby bylo datum co nejblíž dnešku."""
    nejlepsi = None
    for rok in (dnes.year - 1, dnes.year, dnes.year + 1):
        try:
            d = datetime.date(rok, mesic, den)
        except ValueError:
            continue
        if nejlepsi is None or abs((d - dnes).days) < abs((nejlepsi - dnes).days):
            nejlepsi = d
    return nejlepsi.isoformat() if nejlepsi else None


def platnost(radky, cely, dnes):
    """Najde text o platnosti akce a vrátí (text, od, do)."""
    text = None
    for r in radky:
        if "Kč" in r or "%" in r:
            continue
        if RE_DATUM.search(r) or re.search(r"\b(dnes|zítra)\b", r, re.I):
            text = r
            break
    if text is None:
        m = re.search(r"platí\s+(?:do|od)\s+\D{0,14}\d{1,2}\.\s*\d{1,2}\.", cely, re.I)
        if m:
            text = m.group(0)
    if text is None:
        return None, None, None
    data = [datum_iso(int(d), int(m), dnes) for d, m in RE_DATUM.findall(text)]
    data = [d for d in data if d]
    od = do = None
    if len(data) >= 2:
        od, do = data[0], data[1]
    elif len(data) == 1:
        if re.search(r"\bod\b", text, re.I) and not re.search(r"\bdo\b", text, re.I):
            od = data[0]
        else:
            do = data[0]
    elif re.search(r"\bdnes\b", text, re.I):
        do = dnes.isoformat()
    elif re.search(r"\bzítra\b", text, re.I):
        do = (dnes + datetime.timedelta(days=1)).isoformat()
    return text, od, do


# ---------------------------------------------------------------- ROZBOR STRÁNKY
class KupiParser(HTMLParser):
    """
    Čte stránku Kupi.cz od začátku do konce a orientuje se podle odkazů:
      odkaz na /sleva/...   = začíná nový produkt
      odkaz na /letaky/...  = začíná nová nabídka obchodu u toho produktu
      odkaz na #123456      = číslo nabídky (tlačítko Přidat), za ním bývá poznámka
    Text mezi odkazy (cena, množství, platnost) si ukládá k aktuální nabídce.
    Díky tomu nezávisí na názvech CSS tříd, které se na webu často mění.
    """

    def __init__(self, detail_url=None):
        super().__init__(convert_charrefs=True)
        self.detail_url = detail_url   # stránka jednoho produktu: název je v nadpisu h1
        self.h1 = None
        self.v_h2 = False              # jsme uvnitř nadpisu h2? (tam jsou názvy produktů ve výsledcích hledání)
        self.pid = None                # číslo produktu na Kupi.cz, potřebné pro historii cen
        self.bezne = {}                # běžná cena podle velikosti balení, např. {"0.5 l": 34.16}
        self.produkty = []
        self.produkt = None
        self.nabidka = None
        self.odkaz = None
        self.preskoc = 0
        self.dalsi = None

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style"):
            self.preskoc += 1
            return
        if tag == "h2":
            self.v_h2 = True
        if tag == "h1" and self.detail_url and not self.produkty:
            self.h1 = []
        elif tag == "input" and self.detail_url and dict(attrs).get("id") == "product_id":
            self.pid = dict(attrs).get("value")
        elif tag == "a":
            d = dict(attrs)
            if self.detail_url and d.get("data-key") and d.get("data-price") and d["data-key"] != "vse":
                cena = cislo(d["data-price"])
                if cena:
                    self.bezne[d["data-key"].replace("-", " ")] = cena
            self.odkaz = {"href": d.get("href") or "", "text": [], "img": False}
        elif tag == "img" and self.odkaz is not None:
            self.odkaz["img"] = True

    def handle_endtag(self, tag):
        if tag in ("script", "style"):
            self.preskoc = max(0, self.preskoc - 1)
        elif tag == "h2":
            self.v_h2 = False
        elif tag == "h1" and self.h1 is not None:
            nazev, self.h1 = cisti(" ".join(self.h1)), None
            if nazev:
                self.produkt = {"nazev": nazev, "url": self.detail_url, "_text": [], "_nabidky": []}
                self.produkty.append(self.produkt)
        elif tag == "a" and self.odkaz is not None:
            o, self.odkaz = self.odkaz, None
            self._odkaz(o)

    def handle_data(self, data):
        if self.preskoc:
            return
        t = cisti(data)
        if not t:
            return
        if self.h1 is not None:
            self.h1.append(t)
        elif self.odkaz is not None:
            self.odkaz["text"].append(t)
        elif self.nabidka is not None:
            self.nabidka["_pozn" if self.nabidka["id"] else "_text"].append(t)
        elif self.produkt is not None:
            self.produkt["_text"].append(t)

    def _odkaz(self, o):
        href = o["href"]
        text = " ".join(o["text"]).strip()
        if "Načíst další" in text:
            self.dalsi = href
        elif "/sleva/" in href:
            if o["img"] or not text or text.startswith("Další akce"):
                return
            url = absolutni(href).split("#")[0].split("?")[0]
            if self.produkt is not None and self.produkt["url"] == url:
                return
            self.produkt = {"nazev": text, "url": url, "_text": [], "_nabidky": [], "_h2": self.v_h2}
            self.produkty.append(self.produkt)
            self.nabidka = None
        elif "/letaky/" in href:
            if o["img"] or not text or self.produkt is None:
                return
            slug = re.split(r"[/?#]", href.split("/letaky/", 1)[1])[0]
            self.nabidka = {"obchod": slug, "obchod_nazev": text, "id": None,
                            "letak": None, "_text": [], "_pozn": []}
            self.produkt["_nabidky"].append(self.nabidka)
        elif "/letak/" in href:
            if self.nabidka is not None and not self.nabidka["letak"]:
                self.nabidka["letak"] = absolutni(href)
        elif re.fullmatch(r"#\d+", href):
            if self.nabidka is not None and not self.nabidka["id"]:
                self.nabidka["id"] = href[1:]


def zpracuj_nabidku(n, dnes):
    radky = n["_text"]
    cely = " ".join(radky)
    m = RE_CENA.search(cely) or RE_CENA_NOUZE.search(cely)
    if not m:
        return None
    cena = cislo(m.group(1))
    if not cena:
        return None
    mm = RE_MNOZSTVI.match(cely, m.end())
    mnozstvi = cisti(mm.group(1)) if mm else None

    cena_za = jednotka = None
    vsechny = RE_JEDNOTKA.findall(cely)
    if vsechny:
        c, kolik, j = vsechny[-1]
        c, kolik, j = cislo(c), cislo(kolik), j.lower()
        if c and kolik:
            if j == "g":
                kolik, j = kolik / 1000, "kg"
            elif j == "ml":
                kolik, j = kolik / 1000, "l"
            cena_za, jednotka = round(c / kolik, 2), j

    sleva = RE_SLEVA.search(cely)
    text_platnosti, od, do = platnost(radky, cely, dnes)
    pozn = n["_pozn"][0] if n["_pozn"] and not RE_STOP.search(n["_pozn"][0]) else None
    if pozn and len(pozn) > 140:
        pozn = None
    popis = cely + " " + " ".join(n["_pozn"][:2])
    obal = next((nazev for nazev, vzor in RE_OBAL if vzor.search(popis)), None)
    return {
        "id": n["id"],
        "obal": obal,
        "obchod": n["obchod"],
        "obchod_nazev": n["obchod_nazev"],
        "cena": cena,
        "mnozstvi": mnozstvi,
        "cena_za": cena_za,
        "jednotka": jednotka,
        "sleva": int(sleva.group(1)) if sleva else None,
        "klub": bool(RE_KLUB.search(cely + " " + (pozn or ""))),
        "platnost": text_platnosti,
        "plati_od": od,
        "plati_do": do,
        "poznamka": pozn,
        "letak": n["letak"],
    }


RE_BEZNE_STOJI = re.compile(r"(\d+(?:[.,]\d+)?\s*[^\W\d_]+)?\s*běžně stojí\s*(\d[\d ]*,\d{2})\s*Kč")


def rozeber(html, dnes=None, detail_url=None, i_bez_akce=False):
    """Z HTML stránky vrátí (seznam produktů s nabídkami, odkaz na další stránku)."""
    dnes = dnes or datetime.date.today()
    p = KupiParser(detail_url)
    p.feed(html)
    p.close()
    vysledek = []
    for pr in p.produkty:
        nabidky, videne = [], set()
        # skutečná nabídka má tlačítko Přidat s číslem; odkazy na obchody v běžném textu ho nemají
        s_cislem = any(n["id"] for n in pr["_nabidky"])
        for n in pr["_nabidky"]:
            if s_cislem and not n["id"]:
                continue
            z = zpracuj_nabidku(n, dnes)
            if not z:
                continue
            klic = z["id"] or (z["obchod"], z["cena"], z["mnozstvi"], z["plati_do"], z["klub"])
            if klic in videne:      # stejná akce bývá na stránce dvakrát (doporučené + dle ceny)
                continue
            videne.add(klic)
            nabidky.append(z)
        if not nabidky and pr["url"] != detail_url and not (i_bez_akce and pr.get("_h2")):
            continue
        m = RE_BEZNA.search(" ".join(pr["_text"]))
        bezna = cislo(m.group(1)) if m else None
        velikost = next((t for t in pr["_text"][:2] if RE_VELIKOST.fullmatch(t)), None)
        vysledek.append({
            "nazev": pr["nazev"],
            "mnozstvi": velikost,
            "url": pr["url"],
            "bezna_cena": bezna if bezna else None,
            "nabidky": nabidky,
        })
    if detail_url:
        vysledek = [v for v in vysledek if v["url"] == detail_url][:1]
        for v in vysledek:
            v["pid"] = p.pid if p.pid and p.pid.isdigit() else None
            v["bezne_ceny"] = p.bezne
        if vysledek and not vysledek[0]["bezna_cena"]:
            # na stránce produktu je běžná cena ve větě „… 1000 g běžně stojí 42,90 Kč“
            m = RE_BEZNE_STOJI.search(cisti(re.sub(r"<[^>]+>", " ", html)))
            if m:
                vysledek[0]["bezna_cena"] = cislo(m.group(2)) or None
                if m.group(1) and not vysledek[0]["mnozstvi"]:
                    vysledek[0]["mnozstvi"] = cisti(m.group(1))
    return vysledek, p.dalsi


# ---------------------------------------------------------------- STAHOVÁNÍ
# ---- Certifikáty: některé weby (Lidl) neposílají celý řetězec certifikátů. Prohlížeč si chybějící
# mezičlánek sám dohledá, Python ne. Tady ho dohledáme taky: adresu najdeme v certifikátu serveru,
# stáhneme ho a přidáme k ověřování. Ověřování se tím nevypíná, jen doplní chybějící kus.
_ssl_kontexty = {}


# Kořenový certifikát SwissSign (Lidl). Je veřejný a důvěryhodný, jen ho starší Windows ještě nemusí znát.
# Stažený z crt.sh, platí do roku 2047. Přidává se k běžným certifikátům systému, nic nenahrazuje.
DALSI_CERTIFIKATY = """
-----BEGIN CERTIFICATE-----
MIIFkzCCA3ugAwIBAgIUQ/oMX04bgBhE79G0TzUfRPSA7cswDQYJKoZIhvcNAQEL
BQAwUTELMAkGA1UEBhMCQ0gxFTATBgNVBAoTDFN3aXNzU2lnbiBBRzErMCkGA1UE
AxMiU3dpc3NTaWduIFJTQSBUTFMgUm9vdCBDQSAyMDIyIC0gMTAeFw0yMjA2MDgx
MTA4MjJaFw00NzA2MDgxMTA4MjJaMFExCzAJBgNVBAYTAkNIMRUwEwYDVQQKEwxT
d2lzc1NpZ24gQUcxKzApBgNVBAMTIlN3aXNzU2lnbiBSU0EgVExTIFJvb3QgQ0Eg
MjAyMiAtIDEwggIiMA0GCSqGSIb3DQEBAQUAA4ICDwAwggIKAoICAQDLKmjiC8NX
vDVjvHClO/OMPE5Xlm7DTjak9gLKHqquuN6orx122ro10JFwB9+zBvKK8i5VUXu7
LCTLf5ImgKO0lPaCoaTo+nUdWfMHamFk4saMla+ju45vVs9xzF6BYQ1t8qsCLqSX
5XH8irCRIFucdFJtrhUnWXjyCcplDn/L9Ovn3KlMd/YrFgSVrpxxpT8q2kFC5zyE
EPThPYxr4iuRR1VPuFa+Rd4iUU1OKNlfGUEGjw5NBuBwQCMBauTLE5tzrE0USJIt
/m2n+IdreXXhvhCxqohAWVTXz8TQm0SzOGlkjIHRI36qOTw7D59Ke4LKa2/KIj4x
0LDQKhySio/YGZxH5D4MucLNvkEM+KRHBdvBFzA4OmnczcNpI/2aDwLOEGrOyvi5
KaM2iYauC8BPY7kGWUleDsFpswrzd34unYyzJ5jSmY0lpx+Gs6ZUcDj8fV3oT4MM
0ZPlEuRU2j7yrTrePjxF8CgPBrnh25d7mUWe3f6VWQQvdT/TromZhqwUtKiE+shd
OxtYk8EXlFXIC+OCeYSf8wCENO7cMdWP8vpPlkwGqnj73mSiI80fPsWMvDdUDrta
clXvyFu1cvh43zcgTFeRc5JzrBh3Q4IgaezprClG5QtO+DdziZaKHG29777YtvTK
wP1H8K4LWCDFyB02rpeNUIMmJCn3nTsPBQIDAQABo2MwYTAPBgNVHRMBAf8EBTAD
AQH/MA4GA1UdDwEB/wQEAwIBBjAfBgNVHSMEGDAWgBRvjmKLk0Ow4UD2p8P98Q+4
DxU4pTAdBgNVHQ4EFgQUb45ii5NDsOFA9qfD/fEPuA8VOKUwDQYJKoZIhvcNAQEL
BQADggIBAKwsKUF9+lz1GpUYvyypiqkkVHX1uECry6gkUSsYP2OprphWKwVDIqO3
10aewCoSPY6WlkDfDDOLazeROpW7OSltwAJsipQLBwJNGD77+3v1dj2b9l4wBlgz
Hqp41eZUBDqyggmNzhYzWUUo8aWjlw5DI/0LIICQ/+Mmz7hkkeUFjxOgdg3XNwwQ
iJb0Pr6VvfHDffCjw3lHC1ySFWPtUnWK50Zpy1FVCypM9fJkT6lc/2cyjlUtMoIc
gC9qkfjLvH4YoiaoLqNTKIftV+Vlek4ASltOU8liNr3CjlvrzG4ngRhZi0Rjn9UM
ZfQpZX+RLOV/fuiJz48gy20HQhFRJjKKLjpHE7iNvUcNCfAWpO2Whi4Z2L6MOuhF
LhG6rlrnub+xzI/goP+4s9GFe3lmozm1O2bYQL7Pt2eLSMkZJVX8vY3PXtpOpvJp
zv1/THfQwUY1mFwjmwJFQ5Ra3bxHrSL+ul4vkSkphnsh3m5kt8sNjzdbowhq6/Td
Ao9QAwKxuDdollDruF/UKIqlIgyKhPBZLtU30WHlQnNYKoH3dtvi4k0NX/a3vgW0
rk4N3hY9A4GzJl5LuEsAz/+MF7psYC0nhzck5npgL7XTgwSqT0N1osGDsieYK7EO
gLrAhV5Cud+xYJHT6xh+cHiudoO+cVrQkOPKwRYlZ0rwtnu64ZzZ
-----END CERTIFICATE-----
-----BEGIN CERTIFICATE-----
MIIGkzCCBHugAwIBAgIULa4PojoMOF/785XA2QNkLRQYTS4wDQYJKoZIhvcNAQEL
BQAwUTELMAkGA1UEBhMCQ0gxFTATBgNVBAoTDFN3aXNzU2lnbiBBRzErMCkGA1UE
AxMiU3dpc3NTaWduIFJTQSBUTFMgUm9vdCBDQSAyMDIyIC0gMTAeFw0yMjA2Mjkw
OTMwNDdaFw0zNjA2MjkwOTMwNDdaMFAxCzAJBgNVBAYTAkNIMRUwEwYDVQQKEwxT
d2lzc1NpZ24gQUcxKjAoBgNVBAMTIVN3aXNzU2lnbiBSU0EgVExTIEVWIElDQSAy
MDIyIC0gMTCCAiIwDQYJKoZIhvcNAQEBBQADggIPADCCAgoCggIBAL61hlRf7Jxo
0msjavo1pgChwWBDYix5Zd0CnhciVYUCk30Ko6BxFBICoSsZ1gXGqlT20g/AYqYL
xuKcdNNAJ/LHT6k2zL3UhSpx+eHjeTGQ7id2jC1HKRZ9zA8YXdhtY3oJom7B3ykE
d/j0KVmHy9tP1A0rt3ntbJLfLIS6uWogx2KfFs8MwtoAZLiGvp49SHly6p450fcz
payPIWu12PfVQjLg7b9NitlDlYEWiCAL7R3jINw2yMwcdBvq2gy+ZZsiYkSb1m+h
ABOGxU6SCN6w7GgRWWveSaJBvRokUvIon/wsZK51j8RM4TsoR60Wei8ftSBL75BI
g9Us8dkBXDa8vqoDVpc9zs6pan5XN8KymNT52j4gEe161eYTtbiME4KdSWtVsA7e
rdkHsXKJTRIxxdpUkQXxhLXEoyDed/BVgV1yhTeN6YCFX7AiocAi5rPUplc6LV58
CCUWFMSWEJxOYQUrwWFLNzQMnE969hnvdhuO8ZeqtpwFwX/OLryWoil+jGobRm/1
OQS9+urcVygrzZ9Dy9Q/OF/oq9NeaijvL2Ncjkj5f6uJzgXkm7PwjnHrL2FWBkhp
oM/vyT1VAgWNoku3jIyedtyJ9lUECwPIzQuddQYOL8FwhaFmvtHnOLpiy2ctbwir
gJW+KcsNkpHg0N5stJcPzPvlssmNBHbNAgMBAAGjggFiMIIBXjBcBggrBgEFBQcB
AQRQME4wTAYIKwYBBQUHMAKGQGh0dHA6Ly9haWEuc3dpc3NzaWduLmNoL2Fpci1h
ZWZmMzc0ZC0wZjdhLTRjNTUtYTAzNC0xNDQwMjkwY2ZhMzIwEgYDVR0TAQH/BAgw
BgEB/wIBADAoBgNVHSAEITAfMAcGBWeBDAEBMAgGBgQAj3oBBDAKBghghXQBWQIB
AzBRBgNVHR8ESjBIMEagRKBChkBodHRwOi8vY3JsLnN3aXNzc2lnbi5jaC9jZHAt
OTY2MWMyOWYtOTEyMS00ZjQ2LWFjZDgtZWFkNGEyMmY3MTYwMB0GA1UdJQQWMBQG
CCsGAQUFBwMBBggrBgEFBQcDAjAOBgNVHQ8BAf8EBAMCAQYwHQYDVR0OBBYEFElS
3zCGkllfNJwlSCSrwOvRBvLWMB8GA1UdIwQYMBaAFG+OYouTQ7DhQPanw/3xD7gP
FTilMA0GCSqGSIb3DQEBCwUAA4ICAQBugn943V4fbEbG+Leb4YXTWLLfPIC+mrdc
H6v1+Iws+XCzoKthaDk0c346mSaXZM9to5xDOWgfEnBYbVioMyI/5EABbg4ARkgp
dj50FPe9MtLD4kOZFv/8LoRH+WdAfQUsxS1RQincUnYWAxmRNOHLdnbyiQt3sYDl
6tZzURSMnMUec4stxfLT4VQE1Ew6Phr06CouYOd5ON+mWkFhROz3jx5PTXcECrqQ
IT27wJ4mzKA6W9p69ZDFi/+FcpN9vCjzksi0w8i62DwtbO8Pj3ZEOL8z6+cwXyT7
X7Zt96vufj+bsxFo1IXQ6cb2i13qpThSHL4NA1NhUbB/ipMbxNtBJ4fwtcG8SAUs
jRXgG/RYrXRorG90KU/dcezixY4yKnlIdkkhpV7h8jY2+XS7GbjaKee8pPeAFXgs
Hzdi+EhZvHOVfshaKL2CAELrYn8Tzo2Zt9zsbif8L7bPJROS3xqzn+GbCFt67/8Y
jTh84Taa4D49H6V+p01QPkvG7ub7Rw52fm56zY3mabbhbsREOceswsfunxSN/SOE
pLKVMopuVnRcwVIWmnzH9BlBhIzLqOS4kCYA5E5Irw217j/JTGVWEdMN0ar09nGh
WA2Eq8aDANjAP1bao/4nmxsFU2zKbTR40Tb7/HKB5jaItYdkz6ppnxQDLTWe7T6+
nGZwqmYtbQ==
-----END CERTIFICATE-----
"""


def _zakladni_kontext():
    k = ssl.create_default_context()
    try:
        k.load_verify_locations(cadata=DALSI_CERTIFIKATY)
    except ssl.SSLError:
        pass
    return k


def _ssl_kontext(host):
    return _ssl_kontexty.get(host.split(":")[0]) or _zakladni_kontext()


def _doplnit_mezicertifikat(host):
    host = host.split(":")[0]
    if host in _ssl_kontexty:
        return False
    try:
        nejisty = ssl.create_default_context()
        nejisty.check_hostname = False
        nejisty.verify_mode = ssl.CERT_NONE            # jen ke čtení certifikátu, žádná data se tak neposílají
        with socket.create_connection((host, 443), timeout=10) as sock:
            with nejisty.wrap_socket(sock, server_hostname=host) as tls:
                der = tls.getpeercert(binary_form=True)
        adresy = re.findall(rb"http://[\x21-\x7e]+?\.(?:crt|cer|der|p7c)", der)
        if not adresy:
            return False
        with urllib.request.urlopen(adresy[0].decode("ascii"), timeout=10) as r:
            mezi = r.read()
        pem = mezi.decode("ascii") if mezi.startswith(b"-----") else ssl.DER_cert_to_PEM_cert(mezi)
        kontext = _zakladni_kontext()
        kontext.load_verify_locations(cadata=pem)
        _ssl_kontexty[host] = kontext
        return True
    except Exception:
        _ssl_kontexty[host] = None
        return False


_zamky = {}                     # jeden zámek a čas posledního dotazu pro každý web
_zamky_zamek = threading.Lock()


def stahni(url, data=None, limit=25, hlavicky=None):
    """Stáhne jednu stránku. Na každý web jdou dotazy po jednom a s pauzou, ať ho nezatěžujeme.
    Různé weby se ale můžou ptát zároveň."""
    host = urllib.parse.urlparse(url).netloc
    with _zamky_zamek:
        zamek = _zamky.setdefault(host, [threading.Lock(), 0.0])
    with zamek[0]:
        cekat = PAUZA - (time.time() - zamek[1])
        if cekat > 0:
            time.sleep(cekat)
        try:
            h = {"User-Agent": UA, "Accept-Language": "cs"}
            h.update(hlavicky or {})
            req = urllib.request.Request(url, data=data, headers=h)
            try:
                with urllib.request.urlopen(req, timeout=limit, context=_ssl_kontext(host)) as r:
                    return r.read().decode(r.headers.get_content_charset() or "utf-8", "replace")
            except urllib.error.URLError as e:
                if not isinstance(e.reason, ssl.SSLCertVerificationError) or not _doplnit_mezicertifikat(host):
                    raise
                with urllib.request.urlopen(req, timeout=limit, context=_ssl_kontext(host)) as r:
                    return r.read().decode(r.headers.get_content_charset() or "utf-8", "replace")
        finally:
            zamek[1] = time.time()


def hledej(dotaz):
    """Vyhledá na Kupi.cz zboží v akci a vrátí seznam produktů."""
    produkty, podle_url = [], {}
    posledni_html = ""
    for strana in range(1, MAX_STRAN + 1):
        parametry = {"f": dotaz, "vse": 0}
        if strana > 1:
            parametry["page"] = strana
        posledni_html = stahni(ZAKLAD + "/hledej?" + urllib.parse.urlencode(parametry))
        nalezene, dalsi = rozeber(posledni_html)
        for pr in nalezene:
            if pr["url"] in podle_url:
                stary = podle_url[pr["url"]]
                znamy = {n["id"] for n in stary["nabidky"] if n["id"]}
                stary["nabidky"] += [n for n in pr["nabidky"] if not n["id"] or n["id"] not in znamy]
            else:
                podle_url[pr["url"]] = pr
                produkty.append(pr)
        if not nalezene or not dalsi:
            break
    if not produkty:
        # V akci nic není. Zeptáme se ještě na všechno zboží, které Kupi.cz pod tím názvem zná,
        # aby šlo poznat „není v letáku“ od „takové zboží neexistuje“.
        posledni_html = stahni(ZAKLAD + "/hledej?" + urllib.parse.urlencode({"f": dotaz}))
        produkty = rozeber(posledni_html, i_bez_akce=True)[0][:25]
    if not produkty:
        # Uložíme stránku, aby šlo zjistit, jestli opravdu nic není v akci, nebo se změnil web.
        try:
            with open(LADENI_SOUBOR, "w", encoding="utf-8") as f:
                f.write(posledni_html)
        except OSError:
            pass
    return produkty


# ---------------------------------------------------------------- PAMĚŤ (CACHE)
_zamek_cache = threading.Lock()
try:
    with open(CACHE_SOUBOR, encoding="utf-8") as _f:
        CACHE = json.load(_f)
except (OSError, ValueError):
    CACHE = {}


def pamet_cti(klic, hodin):
    with _zamek_cache:
        z = CACHE.get(klic)
    return z if z and time.time() - z["cas"] < hodin * 3600 else None


def pamet_zapis(klic, zaznam):
    ted = time.time()
    zaznam["cas"] = ted
    with _zamek_cache:
        CACHE[klic] = zaznam
        for k in [k for k, v in CACHE.items() if ted - v["cas"] > 7 * 86400]:
            del CACHE[k]
        try:
            with open(CACHE_SOUBOR, "w", encoding="utf-8") as f:
                json.dump(CACHE, f, ensure_ascii=False)
        except OSError:
            pass
    return zaznam


def hledej_s_pameti(dotaz, cerstve=False):
    klic = cisti(dotaz).lower()
    z = None if cerstve else pamet_cti(klic, CACHE_HODIN)
    if z and "produkty" in z:
        return {"dotaz": dotaz, "cas": z["cas"], "z_pameti": True, "produkty": z["produkty"]}
    z = pamet_zapis(klic, {"produkty": hledej(klic)})
    return {"dotaz": dotaz, "cas": z["cas"], "z_pameti": False, "produkty": z["produkty"]}


def produkty_s_pameti(slugy, cerstve=False):
    """Stáhne přímo stránky zapamatovaných produktů. Tam jsou všechny jejich akce, ne jen výběr."""
    produkty, cas = [], time.time()
    for slug in slugy[:15]:
        if not re.fullmatch(r"[a-z0-9-]{1,120}", slug):
            continue
        klic = "@produkt:" + slug
        z = None if cerstve else pamet_cti(klic, CACHE_HODIN)
        if not z or "produkt" not in z:
            url = ZAKLAD + "/sleva/" + slug
            try:
                nalezene, _ = rozeber(stahni(url), detail_url=url)
            except urllib.error.HTTPError as e:
                if e.code != 404:
                    raise
                nalezene = []      # produkt už na Kupi.cz není
            z = pamet_zapis(klic, {"produkt": nalezene[0] if nalezene else None})
        if z["produkt"]:
            produkty.append(z["produkt"])
            cas = min(cas, z["cas"])
    return {"produkty": produkty, "cas": cas}


# ---------------------------------------------------------------- E-SHOPY
# Běžné ceny celého sortimentu, nejen akce. Každý obchod má jinou podobu dat,
# ale všechno se převádí na stejný tvar jako produkty z Kupi.cz.
PROHLIZEC = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
                           "Chrome/131.0 Safari/537.36",
             "Accept": "application/json, text/html;q=0.9, */*;q=0.8"}
RE_MULTI = re.compile(r"(\d+)\s*[x×]\s*(\d+(?:[.,]\d+)?)\s*(kg|g|ml|l|ks)\b", re.I)
RE_VELIK = re.compile(r"(\d+(?:[.,]\d+)?)\s*(kg|g|ml|l|ks)\b", re.I)
RE_OBAL_E = [("plech", re.compile(r"\bplech", re.I)), ("pet", re.compile(r"\bpet\b", re.I)),
             ("sklo", re.compile(r"\bsklo\b|sklen|vratn|\bl[aá]hev", re.I))]


def velikost_z_nazvu(nazev):
    """'Pilsner 6x0,5 l' -> '6x 0,5 l', 'Rohlík 43g' -> '43 g'"""
    m = RE_MULTI.search(nazev)
    if m:
        return "%sx %s %s" % (m.group(1), m.group(2), m.group(3).lower())
    vsechny = RE_VELIK.findall(nazev)
    return "%s %s" % (vsechny[-1][0], vsechny[-1][1].lower()) if vsechny else None


def nabidka_e(obchod, nazev_obchodu, cena, mnozstvi, nazev, url, **dalsi):
    n = {"id": None, "obchod": obchod, "obchod_nazev": nazev_obchodu, "cena": round(float(cena), 2),
         "mnozstvi": mnozstvi, "cena_za": None, "jednotka": None, "sleva": None, "klub": False,
         "platnost": None, "plati_od": None, "plati_do": None, "poznamka": None, "letak": url,
         "eshop": True, "volne": None,
         "obal": next((k for k, v in RE_OBAL_E if v.search(nazev)), None)}
    n.update(dalsi)
    return n


def volne_nabidky(obchod, nazev_obchodu, za_kus, za_kg, nazev, url, **dalsi):
    """Zboží na váhu (ovoce, zelenina): jedna nabídka za kus, druhá za kilo.
    Aplikace si vybere tu, která odpovídá tomu, jak to zboží chceš."""
    vystup = []
    if za_kus:
        vystup.append(nabidka_e(obchod, nazev_obchodu, za_kus, "1 ks", nazev, url, volne="ks", **dalsi))
    if za_kg:
        vystup.append(nabidka_e(obchod, nazev_obchodu, za_kg, "1 kg", nazev, url, volne="kg", **dalsi))
    return vystup


def datum_z(text):
    m = re.match(r"(\d{4}-\d{2}-\d{2})", str(text or ""))
    return m.group(1) if m else None


def eshop_rohlik(dotaz):
    url = "https://www.rohlik.cz/services/frontend-service/search-metadata?" + urllib.parse.urlencode(
        {"search": dotaz, "offset": 0, "limit": 30, "companyId": 1, "canCorrect": "true"})
    data = json.loads(stahni(url, hlavicky=PROHLIZEC))
    vystup = []
    for p in (data.get("data") or {}).get("productList") or []:
        if p.get("archived") or not p.get("price") or p.get("inStock") is False:
            continue
        nazev, cena = p["productName"], p["price"]["full"]
        odkaz = "https://www.rohlik.cz/" + str(p.get("baseLink") or p["productId"])
        objem = (p.get("textualAmount") or "").replace("cca", "").replace("×", "x").strip()
        nabidky = []
        if p.get("unit") == "kg" and (p.get("semicaliber") or "1 ks" in nazev.replace("1ks", "1 ks")):
            nabidky += volne_nabidky("rohlik-cz", "Rohlík.cz", cena, p["pricePerUnit"]["full"], nazev, odkaz)
        else:
            mn = velikost_z_nazvu(nazev) if RE_MULTI.search(nazev) else (objem or velikost_z_nazvu(nazev))
            nabidky.append(nabidka_e("rohlik-cz", "Rohlík.cz", cena, mn, nazev, odkaz))
            for s in p.get("sales") or []:
                if not s.get("active") or s.get("welcomePrice") or not s.get("price"):
                    continue
                sc = s["price"].get("full") if "full" in s["price"] else s["price"].get("amount")
                if not sc or sc >= cena:
                    continue
                nabidky.append(nabidka_e("rohlik-cz", "Rohlík.cz", sc, mn, nazev, odkaz,
                                         klub=s.get("type") == "premium", sleva=s.get("discountPercentage"),
                                         plati_do=datum_z(s.get("endsAt")),
                                         poznamka="cena pro Rohlík Premium" if s.get("type") == "premium" else "akce na Rohlík.cz"))
        vystup.append({"nazev": nazev, "url": odkaz, "mnozstvi": None, "bezna_cena": None, "nabidky": nabidky, "eshop": "rohlik-cz"})
    return vystup


def eshop_kosik(dotaz):
    url = "https://www.kosik.cz/api/front/page/products/flexible?" + urllib.parse.urlencode(
        {"vendor": 1, "slug": "vyhledavani", "limit": 30, "search_term": dotaz, "platform": "web"})
    data = json.loads(stahni(url, hlavicky=PROHLIZEC))
    polozky = (data.get("products") or {}).get("items") or []
    vystup = []
    for p in polozky:
        if not p.get("price"):
            continue
        nazev, cena = p["name"], p["price"]
        odkaz = "https://www.kosik.cz" + (p.get("url") or "")
        q = p.get("productQuantity") or {}
        ppu = p.get("pricePerUnit") or {}
        nabidky = []
        if q.get("prefix") == "cca" and ppu.get("unit") == "kg":
            nabidky += volne_nabidky("kosik-cz", "Košík.cz", cena, ppu.get("price"), nazev, odkaz)
        else:
            mn = velikost_z_nazvu(nazev) if RE_MULTI.search(nazev) else (
                "%s %s" % (q["value"], q["unit"]) if q.get("value") else velikost_z_nazvu(nazev))
            puvodni = p.get("recommendedPrice") or cena
            akce = puvodni > cena + 0.005
            do = None
            m = re.search(r"do\s*(\d{1,2})\.\s*(\d{1,2})\.", p.get("actionLabel") or "")
            if akce and m:
                do = datum_iso(int(m.group(1)), int(m.group(2)), datetime.date.today())
            nabidky.append(nabidka_e("kosik-cz", "Košík.cz", cena, mn, nazev, odkaz,
                                     sleva=(p.get("percentageDiscount") or None) if akce else None, plati_do=do,
                                     poznamka=(p.get("actionLabel") or "akce na Košík.cz") if akce else None))
            if akce:          # až akce skončí, platí běžná cena
                nabidky.append(nabidka_e("kosik-cz", "Košík.cz", puvodni, mn, nazev, odkaz))
            klub = p.get("loyaltyClubBenefitsPrice")
            if isinstance(klub, dict):
                klub = klub.get("price")
            if isinstance(klub, (int, float)) and 0 < klub < cena:
                nabidky.append(nabidka_e("kosik-cz", "Košík.cz", klub, mn, nazev, odkaz, klub=True,
                                         poznamka="cena pro členy klubu Košík"))
        vystup.append({"nazev": nazev, "url": odkaz, "mnozstvi": None, "bezna_cena": None, "nabidky": nabidky, "eshop": "kosik-cz"})
    return vystup


TESCO_HLAVICKY = {
    "User-Agent": PROHLIZEC["User-Agent"],
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "cs-CZ,cs;q=0.9,en;q=0.8",
    "Upgrade-Insecure-Requests": "1",
    "Sec-Fetch-Dest": "document", "Sec-Fetch-Mode": "navigate", "Sec-Fetch-Site": "none", "Sec-Fetch-User": "?1",
    "sec-ch-ua": '"Chromium";v="131", "Not_A Brand";v="24"', "sec-ch-ua-mobile": "?0", "sec-ch-ua-platform": '"Windows"',
}
RE_CLUBCARD = re.compile(r"(\d[\d ]*,\d{2})\s*Kč\s*s\s*Clubcard", re.I)


def eshop_tesco(dotaz):
    url = "https://nakup.itesco.cz/groceries/cs-CZ/search?" + urllib.parse.urlencode({"query": dotaz})
    html = stahni(url, hlavicky=TESCO_HLAVICKY, limit=35)
    m = re.search(r'<script[^>]*type="application/discover\+json"[^>]*>(.*?)</script>', html, re.S)
    if not m:
        raise ValueError("Tesco změnilo podobu stránky")
    cache = json.loads(m.group(1))["mfe-orchestrator"]["props"]["apolloCache"]
    vystup = []
    for klic, p in cache.items():
        if not klic.startswith("ProductType:") or not p.get("isForSale") or not p.get("price"):
            continue
        nazev, cena = p.get("title") or "", (p["price"] or {}).get("actual")
        if not cena:
            continue
        odkaz = "https://nakup.itesco.cz/shop/cs-CZ/products/" + str(p.get("id"))
        nabidky = []
        if p.get("productType") == "LooseProduce" and p["price"].get("unitOfMeasure") == "kg":
            nabidky += volne_nabidky("tesco", "Tesco", cena, p["price"].get("unitPrice"), nazev, odkaz,
                                     poznamka="cena v e-shopu Tesco, v prodejně se může lišit")
        else:
            mn = velikost_z_nazvu(nazev)
            nabidky.append(nabidka_e("tesco", "Tesco", cena, mn, nazev, odkaz,
                                     poznamka="cena v e-shopu Tesco, v prodejně se může lišit"))
            for ref in p.get("promotions") or []:
                promo = cache.get(ref.get("__ref"), ref) if isinstance(ref, dict) else {}
                pred = ((promo.get("price") or {}).get("beforeDiscount"))
                if pred and pred > cena:          # akce: aktuální cena je akční, po ní platí ta „předtím“
                    nabidky[0].update(sleva=round((1 - cena / pred) * 100), plati_do=datum_z(promo.get("endDate")),
                                      poznamka="akce v e-shopu Tesco, v prodejně se může lišit")
                    nabidky.append(nabidka_e("tesco", "Tesco", pred, mn, nazev, odkaz,
                                             poznamka="cena v e-shopu Tesco, v prodejně se může lišit"))
                c = RE_CLUBCARD.search(promo.get("description") or "")
                if c and cislo(c.group(1)) and cislo(c.group(1)) < cena:
                    nabidky.append(nabidka_e("tesco", "Tesco", cislo(c.group(1)), mn, nazev, odkaz, klub=True,
                                             plati_do=datum_z(promo.get("endDate")), poznamka="cena s Clubcard"))
        vystup.append({"nazev": nazev, "url": odkaz, "mnozstvi": None, "bezna_cena": None, "nabidky": nabidky, "eshop": "tesco"})
    return vystup


GLOBUS_DOTAZ = ("query Hledej($q: String!) { productsSearch(searchInput: {search: $q, isAutocomplete: false, "
                "userIdentifier: \"00000000-0000-0000-0000-000000000000\"}, first: 30) "
                "{ edges { node { name slug isSellingDenied unit { name } price { priceWithVat basicPrice { priceWithVat } } } } } }")


def eshop_globus(dotaz):
    telo = json.dumps({"query": GLOBUS_DOTAZ, "variables": {"q": dotaz}}).encode("utf-8")
    data = json.loads(stahni("https://globusonline.cz/graphql/", data=telo,
                             hlavicky=dict(PROHLIZEC, **{"Content-Type": "application/json"})))
    if data.get("errors"):
        raise ValueError(data["errors"][0].get("message", "chyba"))
    vystup = []
    for e in data["data"]["productsSearch"]["edges"]:
        p = e["node"]
        if p.get("isSellingDenied") or not p.get("price"):
            continue
        nazev, cena = p["name"], float(p["price"]["priceWithVat"])
        odkaz = "https://globusonline.cz" + (p.get("slug") or "")
        jednotka = ((p.get("unit") or {}).get("name") or "").lower()
        if jednotka == "kg":
            nabidky = [nabidka_e("globus", "Globus", cena, "1 kg", nazev, odkaz, volne="kg",
                                 poznamka="cena v e-shopu Globus, v prodejně se může lišit")]
        else:
            mn = velikost_z_nazvu(nazev)
            if not mn and re.search(r"\bvoln[éáý]\b", nazev, re.I):
                mn = "1 ks"
            nabidky = [nabidka_e("globus", "Globus", cena, mn, nazev, odkaz, volne="ks" if mn == "1 ks" else None,
                                 poznamka="cena v e-shopu Globus, v prodejně se může lišit")]
            zakl = float(((p["price"].get("basicPrice") or {}).get("priceWithVat")) or 0)
            if zakl > cena + 0.005:      # akce v e-shopu: přidám i běžnou cenu
                nabidky[0].update(sleva=round((1 - cena / zakl) * 100), poznamka="akce v e-shopu Globus, v prodejně se může lišit")
                nabidky.append(nabidka_e("globus", "Globus", zakl, mn, nazev, odkaz, volne=nabidky[0]["volne"],
                                         poznamka="cena v e-shopu Globus, v prodejně se může lišit"))
        vystup.append({"nazev": nazev, "url": odkaz, "mnozstvi": None, "bezna_cena": None, "nabidky": nabidky, "eshop": "globus"})
    return vystup


RE_ZAKLAD = re.compile(r"1\s*(kg|l)\s*=\s*(\d[\d ]*,\d{2})", re.I)
RE_LIDL_DATA = re.compile(r"od\s*(\d{1,2})\.\s*(\d{1,2})\.\s*-\s*(\d{1,2})\.\s*(\d{1,2})\.")


def eshop_lidl(dotaz):
    """Lidl.cz ukazuje jen část potravin (hlavně aktuální nabídku a „Ceny v klidu“)."""
    url = "https://www.lidl.cz/q/api/search?" + urllib.parse.urlencode(
        {"q": dotaz, "assortment": "CZ", "locale": "cs_CZ", "version": "v2.0.0", "fetchsize": 30})
    text = stahni(url, hlavicky=PROHLIZEC)
    try:
        data = json.loads(text)
    except ValueError:
        return []            # na některá slova Lidl místo výsledků přesměruje na stránku kampaně
    dnes = datetime.date.today()
    vystup = []
    for i in data.get("items") or []:
        g = (i.get("gridbox") or {}).get("data") or {}
        if g.get("category") != "Food" or not (g.get("price") or {}).get("price"):
            continue
        nazev, cena = g.get("fullTitle") or g.get("title") or "", g["price"]["price"]
        odkaz = "https://www.lidl.cz" + (g.get("canonicalPath") or g.get("canonicalUrl") or "")
        bp = (g["price"].get("basePrice") or {}).get("text") or ""
        prvni = re.split(r";|,\s", bp)[0]          # "250 g, 100 g = …" i "0,355 l; 100 ml = …"
        mn = (velikost_z_nazvu(((g["price"].get("packaging") or {}).get("text") or "").replace(" x ", "x"))
              or (velikost_z_nazvu(prvni) if "=" not in prvni else None) or velikost_z_nazvu(nazev))
        z = RE_ZAKLAD.search(bp)
        if not mn and z and cislo(z.group(2)):
            mnoz = cena / cislo(z.group(2))      # 29,90 Kč při 119,60 Kč/kg = 0,25 kg
            mn = "%d %s" % (round(mnoz * 1000), "g" if z.group(1).lower() == "kg" else "ml")
        od = do = None
        odznaky = json.dumps(g.get("stockAvailability") or {}, ensure_ascii=False)
        d = RE_LIDL_DATA.search(odznaky)
        if d:
            od = datum_iso(int(d.group(1)), int(d.group(2)), dnes)
            do = datum_iso(int(d.group(3)), int(d.group(4)), dnes)
        nabidky = [nabidka_e("lidl", "Lidl", cena, mn, nazev, odkaz, plati_od=od, plati_do=do,
                             poznamka="cena z webu Lidl" + (" (aktuální nabídka)" if do else ""))]
        pred = (g["price"].get("discount") or {}).get("deletedPrice") or g["price"].get("oldPrice") or 0
        if pred > cena + 0.005:
            nabidky[0]["sleva"] = round((1 - cena / pred) * 100)
            nabidky.append(nabidka_e("lidl", "Lidl", pred, mn, nazev, odkaz, poznamka="běžná cena z webu Lidl"))
        vystup.append({"nazev": nazev, "url": odkaz, "mnozstvi": None, "bezna_cena": None, "eshop": "lidl", "nabidky": nabidky})
    return vystup


ESHOPY = {"rohlik-cz": ("Rohlík.cz", eshop_rohlik), "kosik-cz": ("Košík.cz", eshop_kosik),
          "tesco": ("Tesco", eshop_tesco), "globus": ("Globus", eshop_globus), "lidl": ("Lidl", eshop_lidl)}


def eshopy_s_pameti(dotaz, cerstve=False):
    """Zeptá se všech e-shopů zároveň. Když jeden nefunguje, ostatní výsledky se vrátí stejně."""
    from concurrent.futures import ThreadPoolExecutor
    dotaz = cisti(dotaz).lower()
    produkty, chyby, cas = [], {}, time.time()

    def jeden(slug):
        klic = "@eshop:%s:%s" % (slug, dotaz)
        z = None if cerstve else pamet_cti(klic, CACHE_HODIN)
        if z and "produkty" in z:
            return z
        return pamet_zapis(klic, {"produkty": ESHOPY[slug][1](dotaz)})

    videne = set()
    with ThreadPoolExecutor(max_workers=len(ESHOPY)) as ex:
        budouci = {slug: ex.submit(jeden, slug) for slug in ESHOPY}
        for slug, f in budouci.items():
            try:
                z = f.result(timeout=60)
                for p in z["produkty"]:
                    if p["url"] not in videne and p["nabidky"]:
                        videne.add(p["url"])
                        produkty.append(p)
                cas = min(cas, z["cas"])
            except Exception as e:
                chyby[slug] = popis_chyby(e, ESHOPY[slug][0])
    return {"produkty": produkty, "chyby": chyby, "cas": cas}


# ---------------------------------------------------------------- HISTORIE CEN
RE_GRAF = re.compile(r"var graph_data\s*=\s*(\{.*?\"\})\s*[,;]", re.S)
RE_BOD = re.compile(r"\[(\d{12,14}), ([\d.]+)")


def rozeber_graf(html, dnes=None):
    """Z odpovědi Kupi.cz na graf vývoje ceny vytáhne denní řady za posledních 60 dní.
    low = nejnižší akční cena toho dne v kterémkoli obchodě (0 = nikde v akci), bef = běžná cena."""
    dnes = dnes or datetime.date.today()
    m = RE_GRAF.search(html)
    if not m:
        return None
    data = json.loads(m.group(1))
    rady = {}
    for klic in ("low", "bef"):
        body = []
        for ts, cena in RE_BOD.findall(str(data.get(klic) or "")):
            # časy jsou půlnoci českého času; +3 h spolehlivě trefí správný den v létě i v zimě
            den = (datetime.datetime(1970, 1, 1) + datetime.timedelta(seconds=int(ts) / 1000 + 3 * 3600)).date()
            if 0 <= (dnes - den).days <= 60:
                body.append([den.isoformat(), float(cena)])
        rady[klic] = body
    return rady


def historie_s_pameti(slug, mnozstvi):
    if not re.fullmatch(r"[a-z0-9-]{1,120}", slug):
        return {"chyba": "Neznámý produkt."}
    mnozstvi = cisti(mnozstvi)[:20]
    klic = "@historie:%s:%s" % (slug, mnozstvi)
    z = pamet_cti(klic, 12)
    if z and "rady" in z:
        return {"rady": z["rady"]}
    nalezene = produkty_s_pameti([slug])["produkty"]
    pid = nalezene[0].get("pid") if nalezene else None
    if not pid:
        return {"rady": None}
    pole = {"graph[product]": pid}
    cisla = re.match(r"(?:\d+\s*[x×]\s*)?(\d+(?:[.,]\d+)?)", mnozstvi)
    if mnozstvi and cisla:
        pole["graph[key]"] = mnozstvi.replace(" ", "-")
        pole["graph[amount]"] = mnozstvi.split(" ")[0]
    html = stahni(ZAKLAD + "/graph", data=urllib.parse.urlencode(pole).encode("utf-8"))
    z = pamet_zapis(klic, {"rady": rozeber_graf(html)})
    return {"rady": z["rady"]}


# ---------------------------------------------------------------- POLOHA A OBCHODY V OKOLÍ
_DIA = {"a": "á", "c": "č", "d": "ď", "e": "éě", "i": "í", "n": "ň", "o": "ó",
        "r": "ř", "s": "š", "t": "ť", "u": "úů", "y": "ý", "z": "ž"}


def bez_diakritiky(text):
    return "".join(c for c in unicodedata.normalize("NFD", text.lower()) if not unicodedata.combining(c))


def _vzor(slovo):
    """'hruska' -> vzor, který najde i 'Hruška' (mapa má názvy s háčky a čárkami)."""
    return "".join("[%s%s%s]" % (c, _DIA[c], _DIA[c].upper()) if c in _DIA else c for c in slovo)


def vzdalenost_km(lat1, lon1, lat2, lon2):
    import math
    a, b = math.radians(lat1), math.radians(lat2)
    h = math.sin((b - a) / 2) ** 2 + math.cos(a) * math.cos(b) * math.sin(math.radians(lon2 - lon1) / 2) ** 2
    return 2 * 6371 * math.asin(math.sqrt(h))


def najdi_obchody(lat, lon, slugy):
    """Pro každý řetězec najde nejbližší pobočku v OpenStreetMap (vzdušnou čarou)."""
    slova = {}
    for s in slugy:
        k = re.sub(r"[^a-z0-9-]", "", s.lower()).split("-")[0]   # 'penny-market' -> 'penny'
        if k:
            slova[s] = k
    if not slova:
        return {}
    vzor = "|".join(sorted({_vzor(k) for k in slova.values()}))
    okoli = "(around:%d,%.5f,%.5f)" % (OKOLI_KM * 1000, lat, lon)
    dotaz = ('[out:json][timeout:30];('
             'nwr["shop"]["brand"~"%s",i]%s;'
             'nwr["shop"~"supermarket|convenience|wholesale|chemist|department_store|general|variety_store"]["name"~"%s",i]%s;'
             ');out center tags;') % (vzor, okoli, vzor, okoli)
    telo = urllib.parse.urlencode({"data": dotaz}).encode("utf-8")
    chyba = None
    for server in OVERPASS:
        try:
            data = json.loads(stahni(server, data=telo, limit=45))
            break
        except Exception as e:   # zkusíme záložní server
            chyba = e
    else:
        raise chyba
    nej = {}
    for el in data.get("elements", []):
        tags = el.get("tags") or {}
        stred = el.get("center") or el
        if "lat" not in stred or "lon" not in stred:
            continue
        nazev = tags.get("name") or tags.get("brand") or ""
        slova_v = set(re.findall(r"[a-z0-9]+", bez_diakritiky(" ".join(
            x for x in (tags.get("brand"), tags.get("name"), tags.get("operator")) if x))))
        km = vzdalenost_km(lat, lon, stred["lat"], stred["lon"])
        ulice = tags.get("addr:street") or tags.get("addr:place") or ""
        cislo_domu = tags.get("addr:housenumber") or ""
        adresa = ", ".join(x for x in ((ulice + " " + cislo_domu).strip(), tags.get("addr:city")) if x)
        for slug, k in slova.items():
            if k in slova_v and (slug not in nej or km < nej[slug]["km"]):
                nej[slug] = {"km": round(km, 2), "nazev": nazev, "adresa": adresa or None,
                             "lat": stred["lat"], "lon": stred["lon"]}
    return nej


def obchody_s_pameti(lat, lon, slugy):
    slugy = sorted(set(slugy))[:60]
    lat, lon = round(lat, 3), round(lon, 3)   # přesnost asi 100 m, víc mapě neposíláme
    klic = "@obchody:%.3f,%.3f:%s" % (lat, lon, ",".join(slugy))
    z = pamet_cti(klic, 24 * 7)
    if not z or "obchody" not in z:
        z = pamet_zapis(klic, {"obchody": najdi_obchody(lat, lon, slugy)})
    return {"obchody": z["obchody"], "polomer_km": OKOLI_KM}


def najdi_adresu(adresa):
    klic = "@adresa:" + cisti(adresa).lower()
    z = pamet_cti(klic, 24 * 7)
    if z and "lat" in z:
        return {"lat": z["lat"], "lon": z["lon"], "nazev": z["nazev"]}
    url = NOMINATIM + "?" + urllib.parse.urlencode(
        {"q": adresa, "format": "jsonv2", "limit": 1, "countrycodes": "cz", "accept-language": "cs"})
    vysledky = json.loads(stahni(url))
    if not vysledky:
        return {"chyba": "Tuhle adresu jsem nenašel. Zkus ji napsat jinak, třeba i s městem."}
    v = vysledky[0]
    nazev = ", ".join(v.get("display_name", adresa).split(", ")[:3])
    z = pamet_zapis(klic, {"lat": float(v["lat"]), "lon": float(v["lon"]), "nazev": nazev})
    return {"lat": z["lat"], "lon": z["lon"], "nazev": z["nazev"]}


def popis_chyby(e, sluzba="Kupi.cz"):
    if isinstance(e, urllib.error.HTTPError):
        if e.code in (401, 403, 429):
            return "%s blokuje automatické dotazy (chyba %s)." % (sluzba, e.code)
        return "%s odpovědělo chybou %s. Zkus to za chvíli znovu." % (sluzba, e.code)
    if isinstance(e, urllib.error.URLError):
        if "CERTIFICATE" in str(e.reason).upper():
            return "%s: nepodařilo se ověřit certifikát webu." % sluzba
        return "Nepodařilo se připojit (%s). Zkontroluj připojení k internetu." % sluzba
    if isinstance(e, TimeoutError):
        return "%s neodpovídá. Zkus to za chvíli znovu." % sluzba
    return "Neočekávaná chyba: %s" % e


# ---------------------------------------------------------------- DIAGNOSTIKA
def _popis_certifikatu(der):
    import tempfile
    pem = ssl.DER_cert_to_PEM_cert(der)
    with tempfile.NamedTemporaryFile("w", suffix=".pem", delete=False) as f:
        f.write(pem)
        cesta = f.name
    try:
        info = ssl._ssl._test_decode_cert(cesta)
    finally:
        os.remove(cesta)
    jmeno = lambda x: ", ".join("%s=%s" % kv for rdn in x for kv in rdn)
    return {"subject": jmeno(info.get("subject", ())), "issuer": jmeno(info.get("issuer", ())),
            "do": info.get("notAfter"), "aia": info.get("caIssuers")}


def diagnostika(host):
    """Proč se nejde spojit s webem: přesná chyba a kdo vydal certifikát, který server posílá."""
    vystup = {"verze": VERZE, "python": sys.version.split()[0], "host": host}
    try:
        with socket.create_connection((host, 443), timeout=10) as sock:
            with _zakladni_kontext().wrap_socket(sock, server_hostname=host) as tls:
                vystup["overeni"] = "v pořádku"
    except Exception as e:
        vystup["overeni"] = "%s: %s" % (type(e).__name__, e)
    try:
        nejisty = ssl.create_default_context()
        nejisty.check_hostname = False
        nejisty.verify_mode = ssl.CERT_NONE
        with socket.create_connection((host, 443), timeout=10) as sock:
            with nejisty.wrap_socket(sock, server_hostname=host) as tls:
                retez = []
                if hasattr(tls, "get_unverified_chain"):
                    retez = [c if isinstance(c, bytes) else c.public_bytes() for c in (tls.get_unverified_chain() or [])]
                if not retez:
                    retez = [tls.getpeercert(binary_form=True)]
                vystup["retez"] = [_popis_certifikatu(c) for c in retez]
    except Exception as e:
        vystup["retez"] = "%s: %s" % (type(e).__name__, e)
    return vystup


# ---------------------------------------------------------------- SERVER
SOUBORY = {   # ikonky a popis aplikace pro „Přidat na plochu“ v telefonu
    "/manifest.webmanifest": ("manifest.webmanifest", "application/manifest+json"),
    "/ikona-180.png": ("ikona-180.png", "image/png"),
    "/ikona-192.png": ("ikona-192.png", "image/png"),
    "/ikona-512.png": ("ikona-512.png", "image/png"),
}


class Obsluha(BaseHTTPRequestHandler):
    def _posli(self, kod, typ, data):
        self.send_response(kod)
        self.send_header("Content-Type", typ)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def _json(self, obj):
        self._posli(200, "application/json; charset=utf-8",
                    json.dumps(obj, ensure_ascii=False).encode("utf-8"))

    def _povoleno(self):
        """Na serveru s nastaveným heslem pustí dál jen toho, kdo heslo zná (jméno je libovolné)."""
        if not HESLO:
            return True
        h = self.headers.get("Authorization") or ""
        if h.startswith("Basic "):
            try:
                zadane = base64.b64decode(h[6:]).decode("utf-8").split(":", 1)[-1]
                if hmac.compare_digest(zadane.encode("utf-8"), HESLO.encode("utf-8")):
                    return True
            except Exception:
                pass
        data = "Papírek je zamčený heslem.".encode("utf-8")
        self.send_response(401)
        self.send_header("WWW-Authenticate", 'Basic realm="Papirek", charset="UTF-8"')
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)
        return False

    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        if u.path == "/zdravi":                     # kontrola, že server žije (pro hosting)
            self._json({"ok": True})
            return
        if not self._povoleno():
            return
        if u.path in SOUBORY:
            jmeno, typ = SOUBORY[u.path]
            try:
                with open(os.path.join(SLOZKA, jmeno), "rb") as f:
                    self._posli(200, typ, f.read())
            except OSError:
                self._posli(404, "text/plain; charset=utf-8", b"Nenalezeno")
        elif u.path in ("/", "/index.html"):
            try:
                with open(os.path.join(SLOZKA, "index.html"), "rb") as f:
                    self._posli(200, "text/html; charset=utf-8", f.read())
            except OSError:
                self._posli(500, "text/plain; charset=utf-8",
                            "Chybí soubor index.html (musí být ve stejné složce jako app.py).".encode("utf-8"))
        elif u.path == "/api/hledej":
            q = urllib.parse.parse_qs(u.query)
            dotaz = cisti((q.get("q") or [""])[0])[:80]
            if not dotaz:
                self._json({"chyba": "Chybí název zboží."})
                return
            try:
                self._json(hledej_s_pameti(dotaz, cerstve=bool(q.get("fresh"))))
            except Exception as e:  # ať aplikace vždy dostane srozumitelnou odpověď
                self._json({"chyba": popis_chyby(e)})
        elif u.path == "/api/verze":
            self._json({"verze": VERZE})
        elif u.path == "/api/konec":
            if V_CLOUDU or self.headers.get("Origin") or self.headers.get("Referer"):
                self._posli(403, "text/plain; charset=utf-8", b"Jen pro novou verzi Papirku")   # ne z webových stránek
                return
            self._json({"ok": True})
            threading.Timer(0.3, lambda: os._exit(0)).start()
        elif u.path == "/api/diag":
            q = urllib.parse.parse_qs(u.query)
            host = re.sub(r"[^a-z0-9.-]", "", (q.get("host") or ["www.lidl.cz"])[0].lower())[:80]
            self._json(diagnostika(host))
        elif u.path == "/api/eshopy":
            q = urllib.parse.parse_qs(u.query)
            dotaz = cisti((q.get("q") or [""])[0])[:80]
            if not dotaz:
                self._json({"chyba": "Chybí název zboží."})
                return
            self._json(eshopy_s_pameti(dotaz, cerstve=bool(q.get("fresh"))))
        elif u.path == "/api/produkty":
            q = urllib.parse.parse_qs(u.query)
            slugy = [x for x in (q.get("slugy") or [""])[0].split(",") if x]
            try:
                self._json(produkty_s_pameti(slugy, cerstve=bool(q.get("fresh"))))
            except Exception as e:
                self._json({"chyba": popis_chyby(e)})
        elif u.path == "/api/historie":
            q = urllib.parse.parse_qs(u.query)
            try:
                self._json(historie_s_pameti((q.get("slug") or [""])[0], (q.get("mnozstvi") or [""])[0]))
            except Exception as e:
                self._json({"chyba": popis_chyby(e)})
        elif u.path == "/api/obchody":
            q = urllib.parse.parse_qs(u.query)
            try:
                lat, lon = float(q["lat"][0]), float(q["lon"][0])
                if not (-90 <= lat <= 90 and -180 <= lon <= 180):
                    raise ValueError
            except (KeyError, ValueError):
                self._json({"chyba": "Chybí poloha."})
                return
            slugy = [s for s in (q.get("slugy") or [""])[0].split(",") if s]
            try:
                self._json(obchody_s_pameti(lat, lon, slugy))
            except Exception as e:
                self._json({"chyba": popis_chyby(e, "Mapa OpenStreetMap")})
        elif u.path == "/api/poloha":
            q = urllib.parse.parse_qs(u.query)
            adresa = cisti((q.get("adresa") or [""])[0])[:120]
            if not adresa:
                self._json({"chyba": "Chybí adresa."})
                return
            try:
                self._json(najdi_adresu(adresa))
            except Exception as e:
                self._json({"chyba": popis_chyby(e, "Mapa OpenStreetMap")})
        else:
            self._posli(404, "text/plain; charset=utf-8", b"Nenalezeno")

    def log_message(self, fmt, *args):
        if "/api/" in (args[0] if args else ""):
            sys.stderr.write("  %s\n" % urllib.parse.unquote(str(args[0])))


def vypis(produkty):
    if not produkty:
        print("Nic v akci jsem nenašel.")
    for pr in produkty:
        print("\n%s  (běžně %s Kč)" % (pr["nazev"], pr["bezna_cena"] or "?"))
        for n in pr["nabidky"]:
            print("   %-20s %8.2f Kč / %-8s %s%s%s" % (
                n["obchod_nazev"], n["cena"], n["mnozstvi"] or "?", n["platnost"] or "",
                "  [klub]" if n["klub"] else "", "  (%s)" % n["poznamka"] if n["poznamka"] else ""))


def ukoncit_stary():
    """Ukončí starší Papírek, který drží port. Nejdřív slušně, pak přes Windows (jen proces Pythonu)."""
    try:
        urllib.request.urlopen("http://127.0.0.1:%d/api/konec" % PORT, timeout=3).read()
        time.sleep(1)
        return
    except Exception:
        pass                       # starší verze tohle neumí
    if os.name != "nt":
        return
    import subprocess
    try:
        vypis_portu = subprocess.run(["netstat", "-ano", "-p", "TCP"], capture_output=True, text=True, timeout=10).stdout
        pidy = {r.split()[-1] for r in vypis_portu.splitlines()
                if ("127.0.0.1:%d " % PORT) in r and "LISTENING" in r.upper()}
        for pid in pidy:
            jmeno = subprocess.run(["tasklist", "/FI", "PID eq %s" % pid, "/FO", "CSV", "/NH"],
                                   capture_output=True, text=True, timeout=10).stdout.lower()
            if "python" in jmeno or "py.exe" in jmeno:       # nic jiného než Python neukončuji
                subprocess.run(["taskkill", "/PID", pid, "/F"], capture_output=True, timeout=10)
    except Exception:
        pass


def main():
    if len(sys.argv) >= 3 and sys.argv[1] == "hledej":
        try:
            vypis(hledej(" ".join(sys.argv[2:])))
        except Exception as e:
            print(popis_chyby(e))
        return
    if len(sys.argv) >= 3 and sys.argv[1] == "soubor":
        with open(sys.argv[2], encoding="utf-8") as f:
            vypis(rozeber(f.read())[0])
        return
    if V_CLOUDU:
        server = ThreadingHTTPServer(("0.0.0.0", PORT), Obsluha)
        print("Papírek běží na serveru, port %d%s" % (PORT, ", zamčeno heslem" if HESLO else ", BEZ HESLA"), flush=True)
        server.serve_forever()
        return
    try:
        server = ThreadingHTTPServer(("127.0.0.1", PORT), Obsluha)
    except OSError:
        # Na portu už něco běží, nejspíš starší Papírek. Ukončím ho, ať běží tahle (novější) verze.
        print("Na portu %d už běží starší Papírek, ukončuji ho…" % PORT)
        ukoncit_stary()
        server = None
        for _ in range(20):
            try:
                server = ThreadingHTTPServer(("127.0.0.1", PORT), Obsluha)
                break
            except OSError:
                time.sleep(0.5)
        if server is None:
            print("Starší Papírek se nepodařilo ukončit. Zavři všechna černá okna Papírku "
                  "(nebo restartuj počítač) a spusť ho znovu.")
            input("Okno zavřeš klávesou Enter.")
            return
    adresa = "http://localhost:%d" % PORT
    print("Papírek běží na %s" % adresa)
    print("Tohle okno nech otevřené. Aplikaci ukončíš klávesami Ctrl+C nebo zavřením okna.")
    threading.Timer(0.8, lambda: webbrowser.open(adresa)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nUkončeno.")


if __name__ == "__main__":
    main()
