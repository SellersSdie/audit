const express = require('express');
const { google } = require('googleapis');
const { Readable } = require('stream');
const multer = require('multer');
const cors = require('cors');
const { parse } = require('csv-parse/sync');
const Anthropic = require('@anthropic-ai/sdk');
const axios = require('axios');
const rateLimit = require('express-rate-limit');

const app = express();
const upload = multer({ storage: multer.memoryStorage(), limits: { fileSize: 50 * 1024 * 1024 } });

app.use(cors());
app.use(express.json());

const limiter = rateLimit({ windowMs: 15 * 60 * 1000, max: 20 });
app.use('/analyse', limiter);

const anthropic = new Anthropic({ apiKey: process.env.ANTHROPIC_API_KEY });

// ─── CSV Parsing ────────────────────────────────────────────────────────────

function parseCSV(buffer) {
  let text = buffer.toString('utf8').replace(/^\uFEFF/, ''); // strip BOM
  try {
    const rows = parse(text, { columns: true, skip_empty_lines: true, trim: true, relax_quotes: true });
    if (rows.length > 0) return rows;
  } catch (e) {}
  try {
    return parse(text, { columns: true, skip_empty_lines: true, trim: true, delimiter: '\t', relax_quotes: true });
  } catch (e) {
    return [];
  }
}

function normaliseHeaders(rows) {
  return rows.map(row => {
    const normalised = {};
    for (const [k, v] of Object.entries(row)) {
      normalised[k.trim().replace(/\s+/g, ' ')] = v;
    }
    return normalised;
  });
}

function detectReportType(headers) {
  const h = new Set(headers.map(x => x.toLowerCase().trim().replace(/\s+/g, ' ')));
  const has = (...keys) => keys.every(k => h.has(k));
  const any = (...keys) => keys.some(k => h.has(k));

  if (any('real-time status', 'estimated missed sales due to budget', 'estimated missed clicks due to budget')) return 'budget';
  if (h.has('placement') && any('campaign name', 'spend')) return 'placement';
  if (h.has('sessions') || h.has('unit session percentage')) return 'business_report';
  if (h.has('search query') && any('impressions - brand share', 'purchases - brand share', 'brand share')) return 'brand_analytics';
  if (any('repeat purchase orders', 'repeat purchase rate', 'new-to-brand orders')) return 'repeat_purchase';
  if (h.has('customer search term') && h.has('campaign name')) {
    const campaignTypeCol = [...h].find(x => x.includes('campaign type') || x.includes('ad type'));
    return 'sp_search_term'; // default; SB won't usually have 'customer search term'
  }
  if (h.has('targeting expression') || any('keyword bid', 'match type')) return 'targeting';
  return 'unknown';
}

// ─── Numeric helper ─────────────────────────────────────────────────────────

function num(v) {
  if (v === null || v === undefined || v === '') return 0;
  return parseFloat(v.toString().replace(/[^0-9.-]/g, '')) || 0;
}

// ─── Report Aggregators ─────────────────────────────────────────────────────

function aggregateSPSearchTerm(rows) {
  let totalSpend = 0, totalSales = 0, totalClicks = 0, totalImpressions = 0, totalOrders = 0;
  const matchType = { exact: { spend: 0, sales: 0, orders: 0 }, phrase: { spend: 0, sales: 0, orders: 0 }, broad: { spend: 0, sales: 0, orders: 0 } };
  const termMap = {};

  for (const row of rows) {
    const spend = num(row['Spend']);
    const sales = num(row['7 Day Total Sales'] || row['14 Day Total Sales'] || row['Sales ($)'] || row['Sales']);
    const clicks = num(row['Clicks']);
    const impressions = num(row['Impressions']);
    const orders = num(row['7 Day Total Orders (#)'] || row['14 Day Total Orders (#)'] || row['Orders']);
    const term = (row['Customer Search Term'] || row['Search Term'] || '').trim();
    const mt = (row['Match Type'] || row['Match type'] || '').toLowerCase().trim();

    totalSpend += spend;
    totalSales += sales;
    totalClicks += clicks;
    totalImpressions += impressions;
    totalOrders += orders;

    if (mt.includes('exact')) { matchType.exact.spend += spend; matchType.exact.sales += sales; matchType.exact.orders += orders; }
    else if (mt.includes('phrase')) { matchType.phrase.spend += spend; matchType.phrase.sales += sales; matchType.phrase.orders += orders; }
    else if (mt.includes('broad')) { matchType.broad.spend += spend; matchType.broad.sales += sales; matchType.broad.orders += orders; }

    if (!termMap[term]) termMap[term] = { spend: 0, sales: 0, orders: 0, clicks: 0 };
    termMap[term].spend += spend;
    termMap[term].sales += sales;
    termMap[term].orders += orders;
    termMap[term].clicks += clicks;
  }

  const nonConvertingTerms = Object.entries(termMap)
    .filter(([, v]) => v.orders === 0 && v.spend > 0)
    .sort((a, b) => b[1].spend - a[1].spend);

  const nonConvertingSpend = nonConvertingTerms.reduce((a, [, v]) => a + v.spend, 0);
  const nonConvertingPct = totalSpend > 0 ? (nonConvertingSpend / totalSpend) * 100 : 0;

  const topConverting = Object.entries(termMap)
    .filter(([, v]) => v.orders > 0)
    .sort((a, b) => b[1].sales - a[1].sales)
    .slice(0, 10)
    .map(([term, d]) => ({ term, ...d, acos: d.sales > 0 ? (d.spend / d.sales) * 100 : 0, cvr: d.clicks > 0 ? (d.orders / d.clicks) * 100 : 0 }));

  return {
    totalSpend, totalSales, totalClicks, totalImpressions, totalOrders,
    acos: totalSales > 0 ? (totalSpend / totalSales) * 100 : 0,
    ctr: totalImpressions > 0 ? (totalClicks / totalImpressions) * 100 : 0,
    cvr: totalClicks > 0 ? (totalOrders / totalClicks) * 100 : 0,
    nonConvertingSpend,
    nonConvertingPct,
    topNonConvertingTerms: nonConvertingTerms.slice(0, 10).map(([term, d]) => ({ term, ...d })),
    topConvertingTerms: topConverting,
    matchTypeBreakdown: matchType,
    uniqueSearchTerms: Object.keys(termMap).length
  };
}

function aggregateBudget(rows) {
  let totalCampaigns = 0, budgetLimited = 0;
  let estimatedMissedSales = 0, estimatedMissedClicks = 0;
  const limitedCampaigns = [];

  for (const row of rows) {
    totalCampaigns++;
    const status = (row['Real-time Status'] || row['Budget Status'] || '').toLowerCase();
    const missedSales = num(row['Estimated Missed Sales due to Budget'] || row['Estimated missed sales due to budget'] || 0);
    const missedClicks = num(row['Estimated Missed Clicks due to Budget'] || 0);
    const campaignName = row['Campaign Name'] || row['Campaign name'] || '';
    const dailyBudget = num(row['Campaign Daily Budget'] || row['Daily Budget'] || 0);

    if (status.includes('out of budget') || status.includes('limited')) {
      budgetLimited++;
      estimatedMissedSales += missedSales;
      estimatedMissedClicks += missedClicks;
      limitedCampaigns.push({ campaignName, missedSales, dailyBudget });
    }
  }

  const budgetLimitedPct = totalCampaigns > 0 ? (budgetLimited / totalCampaigns) * 100 : 0;

  return {
    totalCampaigns, budgetLimited, budgetLimitedPct,
    estimatedMissedSales, estimatedMissedClicks,
    projectedSalesIncrease: budgetLimitedPct >= 20 ? estimatedMissedSales * 0.20 : 0,
    topLimitedCampaigns: limitedCampaigns.sort((a, b) => b.missedSales - a.missedSales).slice(0, 5)
  };
}

function aggregatePlacement(rows) {
  const placements = {};

  for (const row of rows) {
    const placement = (row['Placement'] || row['placement'] || 'Unknown').trim();
    const spend = num(row['Spend']);
    const sales = num(row['7 Day Total Sales'] || row['Sales'] || row['14 Day Total Sales']);
    const clicks = num(row['Clicks']);
    const orders = num(row['7 Day Total Orders (#)'] || row['Orders'] || row['14 Day Total Orders (#)']);
    const impressions = num(row['Impressions']);

    if (!placements[placement]) placements[placement] = { spend: 0, sales: 0, clicks: 0, orders: 0, impressions: 0 };
    placements[placement].spend += spend;
    placements[placement].sales += sales;
    placements[placement].clicks += clicks;
    placements[placement].orders += orders;
    placements[placement].impressions += impressions;
  }

  return Object.entries(placements).map(([name, d]) => ({
    name, ...d,
    acos: d.sales > 0 ? (d.spend / d.sales) * 100 : 0,
    cvr: d.clicks > 0 ? (d.orders / d.clicks) * 100 : 0,
    cpc: d.clicks > 0 ? (d.spend / d.clicks) : 0
  }));
}

function aggregateBusinessReport(rows) {
  let totalSessions = 0, totalOrders = 0, totalSales = 0;
  const asins = [];

  for (const row of rows) {
    const sessions = num(row['Sessions'] || row['Browser Sessions'] || 0);
    const orders = num(row['Units Ordered'] || row['Units ordered'] || 0);
    const sales = num(row['Ordered Product Sales'] || row['Sales'] || 0);
    const asin = (row['(Child) ASIN'] || row['ASIN'] || row['Child ASIN'] || '').trim();
    const title = (row['Title'] || row['Product Name'] || '').substring(0, 70);

    totalSessions += sessions;
    totalOrders += orders;
    totalSales += sales;
    if (asin) asins.push({ asin, title, sessions, orders, sales });
  }

  return {
    totalSessions, totalOrders, totalSales,
    overallCvr: totalSessions > 0 ? (totalOrders / totalSessions) * 100 : 0,
    topAsins: asins.sort((a, b) => b.sales - a.sales).slice(0, 10)
  };
}

function aggregateBrandAnalytics(rows) {
  const queries = [];
  let totalBrandImpShare = 0, count = 0;

  for (const row of rows) {
    const query = (row['Search Query'] || row['Search Term'] || '').trim();
    const volume = num(row['Search Query Volume'] || 0);
    const brandImpShare = num(row['Impressions - Brand Share'] || row['Brand Impression Share'] || 0);
    const brandClickShare = num(row['Clicks - Brand Share'] || row['Brand Click Share'] || 0);
    const brandPurchaseShare = num(row['Purchases - Brand Share'] || row['Brand Purchase Share'] || 0);
    const totalPurchases = num(row['Purchases - Total Count'] || 0);

    if (query) {
      queries.push({ query, volume, brandImpShare, brandClickShare, brandPurchaseShare, totalPurchases });
      totalBrandImpShare += brandImpShare;
      count++;
    }
  }

  const lowShareOpportunities = queries
    .filter(q => q.brandImpShare < 30 && q.volume > 50)
    .sort((a, b) => b.volume - a.volume)
    .slice(0, 10);

  return {
    totalQueries: queries.length,
    avgBrandImpressionShare: count > 0 ? totalBrandImpShare / count : 0,
    lowShareOpportunities,
    topQueryByVolume: queries.sort((a, b) => b.volume - a.volume).slice(0, 10)
  };
}

function aggregateRepeatPurchase(rows) {
  let totalOrders = 0, repeatOrders = 0, ntbOrders = 0, totalSales = 0, repeatSales = 0;

  for (const row of rows) {
    totalOrders += num(row['Orders'] || row['Total Orders'] || 0);
    repeatOrders += num(row['Repeat Purchase Orders'] || row['Repeat Orders'] || 0);
    ntbOrders += num(row['New-to-Brand Orders'] || row['New To Brand Orders'] || 0);
    totalSales += num(row['Ordered Product Sales'] || row['Sales'] || 0);
    repeatSales += num(row['Repeat Purchase Sales'] || row['Repeat Sales'] || 0);
  }

  return {
    totalOrders, repeatOrders, ntbOrders, totalSales, repeatSales,
    repeatPurchaseRate: totalOrders > 0 ? (repeatOrders / totalOrders) * 100 : 0,
    repeatSalesRate: totalSales > 0 ? (repeatSales / totalSales) * 100 : 0
  };
}

function aggregateTargeting(rows) {
  const matchBreakdown = { exact: { spend: 0, sales: 0, orders: 0 }, phrase: { spend: 0, sales: 0, orders: 0 }, broad: { spend: 0, sales: 0, orders: 0 }, auto: { spend: 0, sales: 0, orders: 0 } };

  for (const row of rows) {
    const mt = (row['Match Type'] || row['Match type'] || '').toLowerCase();
    const spend = num(row['Spend']);
    const sales = num(row['7 Day Total Sales'] || row['Sales'] || 0);
    const orders = num(row['7 Day Total Orders (#)'] || row['Orders'] || 0);

    if (mt.includes('exact')) { matchBreakdown.exact.spend += spend; matchBreakdown.exact.sales += sales; matchBreakdown.exact.orders += orders; }
    else if (mt.includes('phrase')) { matchBreakdown.phrase.spend += spend; matchBreakdown.phrase.sales += sales; matchBreakdown.phrase.orders += orders; }
    else if (mt.includes('broad')) { matchBreakdown.broad.spend += spend; matchBreakdown.broad.sales += sales; matchBreakdown.broad.orders += orders; }
    else if (mt.includes('auto')) { matchBreakdown.auto.spend += spend; matchBreakdown.auto.sales += sales; matchBreakdown.auto.orders += orders; }
  }

  return { matchBreakdown };
}

// ─── Benchmark Projections ───────────────────────────────────────────────────

function calculateProjections(aggregated) {
  const projections = {};

  // Ad mix projection (keep SP fixed, project SB and SD up to benchmarks)
  if (aggregated.sp_search_term) {
    const spSales = aggregated.sp_search_term.totalSales;
    const projectedTotal = spSales / 0.65;
    projections.adMix = {
      currentSpSales: spSales,
      benchmarkSp: 0.65,
      benchmarkSb: 0.275,
      benchmarkSd: 0.075,
      projectedSbSales: projectedTotal * 0.275,
      projectedSdSales: projectedTotal * 0.075,
      projectedTotalAdSales: projectedTotal,
      additionalAdRevenue: projectedTotal - spSales
    };
  }

  // Organic projection
  if (aggregated.business_report && aggregated.sp_search_term) {
    const totalSales = aggregated.business_report.totalSales;
    const adSales = aggregated.sp_search_term.totalSales;
    const organicSales = Math.max(0, totalSales - adSales);
    const organicPct = totalSales > 0 ? (organicSales / totalSales) * 100 : 0;
    const benchmark = totalSales > 200000 ? 70 : 50;

    // Correct logic: if organic is below benchmark, organic needs to grow to match ad sales ratio.
    // At 50% benchmark: organic should equal ad sales. Opportunity = how much organic needs to grow.
    // At 70% benchmark: organic / total = 0.70, so total = adSales / (1 - 0.70) = adSales / 0.30
    const benchmarkFraction = benchmark / 100;
    const projectedTotal = adSales / (1 - benchmarkFraction);
    const additionalRevenue = Math.max(0, projectedTotal - totalSales);

    projections.organic = {
      totalSales, adSales, organicSales, organicPct, benchmark,
      isBelowBenchmark: organicPct < benchmark,
      projectedTotalRevenue: organicPct < benchmark ? projectedTotal : totalSales,
      additionalRevenue
    };
  }

  // Non-converting spend vs benchmark
  if (aggregated.sp_search_term) {
    const totalSales = aggregated.business_report?.totalSales || aggregated.sp_search_term.totalSales;
    const benchmark = totalSales > 200000 ? 15 : 30;
    const current = aggregated.sp_search_term.nonConvertingPct;
    const excess = Math.max(0, current - benchmark);
    const excessSpend = aggregated.sp_search_term.totalSpend * (excess / 100);

    projections.wastedSpend = { current, benchmark, excessPct: excess, excessSpend };
  }

  return projections;
}

// ─── System Prompt ───────────────────────────────────────────────────────────

const SYSTEM_PROMPT = `You are a senior Amazon advertising strategist at a leading UK Amazon agency. You analyse account data and produce audit reports that demonstrate elite expertise, uncover real opportunities with precise numbers, and compel the account owner to book a strategy call.

BENCHMARK DATA:
- Non-converting spend: <30% of total spend. For accounts doing >$200k/month total sales: <15%
- Ad type revenue mix: Sponsored Products = 65%, Sponsored Brands = 27.5%, Sponsored Display = 7.5%
- Repeat purchase rate benchmark: 25%+ for consumables, supplements, beauty
- Budget efficiency: If >20% of campaigns run out of budget, project 20% additional sales from resolution
- Organic sales as % of total: ~50% target (accounts >$200k/month: 70%)

PROJECTION RULES (follow exactly):
1. Ad mix: Keep the highest ad type (usually SP) fixed. Project others to match benchmark ratios.
   Example: SP = $100k → projected total = $100k/0.65 = $153,846 → SB = $42,308, SD = $11,538
2. Budget: Only apply if >20% of campaigns are budget-limited. Project 20% uplift on estimated missed sales.
3. Organic: If organic % < benchmark, project total revenue if ad sales stayed fixed but organic reached benchmark ratio.
   Logic: at 50% benchmark, organic = ad sales. Projected total = adSales / (1 - benchmark). Opportunity = projected total - current total.
   Example: Total = £100k, Ad sales = £70k, Organic = £30k (30%). Benchmark = 50%. Projected total = £70k / 0.50 = £140k. Opportunity = £40k.
4. Non-converting spend: Excess spend above benchmark = recoverable capital (not revenue, unless redirected)

OUTPUT ONLY VALID JSON — no prose, no markdown, no backticks. Exact schema:

{
  "accountScore": <0-100 integer>,
  "scoreBreakdown": {
    "adEfficiency": <0-25>,
    "budgetHealth": <0-25>,
    "growthOpportunity": <0-25>,
    "brandStrength": <0-25>
  },
  "headline": "<one punchy sentence: biggest single opportunity this account has>",
  "currency": "<symbol inferred from data, default £>",
  "keyFindings": [
    {
      "title": "<short title>",
      "finding": "<specific insight with actual numbers from the data>",
      "impact": "high|medium|low",
      "projectedValue": "<monetary or % figure, or null>"
    }
  ],
  "adMixAnalysis": {
    "available": true|false,
    "currentSpSales": <number>,
    "currentSbSales": <number or 0>,
    "currentSdSales": <number or 0>,
    "projectedSpSales": <number>,
    "projectedSbSales": <number>,
    "projectedSdSales": <number>,
    "opportunityValue": <number>,
    "insight": "<2-3 sentences specific to this account>"
  },
  "wastedSpendAnalysis": {
    "available": true|false,
    "totalSpend": <number>,
    "nonConvertingSpend": <number>,
    "nonConvertingPct": <number>,
    "benchmark": <number>,
    "excessSpend": <number>,
    "topWastedTerms": [{"term": "<string>", "spend": <number>}],
    "insight": "<specific to their data>"
  },
  "organicGrowthAnalysis": {
    "available": true|false,
    "currentOrganicPct": <number>,
    "benchmark": <number>,
    "currentTotalSales": <number>,
    "projectedTotalSales": <number>,
    "additionalRevenue": <number>,
    "insight": "<specific to their data>"
  },
  "budgetAnalysis": {
    "available": true|false,
    "budgetLimitedPct": <number>,
    "estimatedMissedSales": <number>,
    "projectedSalesIncrease": <number>,
    "topLimitedCampaigns": [{"campaignName": "<string>", "missedSales": <number>}],
    "insight": "<specific to their data>"
  },
  "repeatPurchaseAnalysis": {
    "available": true|false,
    "currentRate": <number>,
    "benchmark": 25,
    "isBelowBenchmark": true|false,
    "insight": "<specific to their data>"
  },
  "placementAnalysis": {
    "available": true|false,
    "placements": [{"name": "<string>", "spend": <number>, "sales": <number>, "acos": <number>, "cvr": <number>}],
    "topOpportunity": "<placement name>",
    "insight": "<specific recommendation>"
  },
  "matchTypeAnalysis": {
    "available": true|false,
    "breakdown": {"exact": {"spend": <number>, "sales": <number>}, "phrase": {"spend": <number>, "sales": <number>}, "broad": {"spend": <number>, "sales": <number>}},
    "insight": "<specific observation about their match type strategy>"
  },
  "brandAnalyticsInsights": {
    "available": true|false,
    "avgBrandImpressionShare": <number>,
    "topOpportunities": [{"query": "<string>", "volume": <number>, "brandImpShare": <number>}],
    "insight": "<specific to their data>"
  },
  "strategicPriorities": [
    {
      "priority": <1-5>,
      "action": "<specific action, not vague>",
      "rationale": "<why this matters for this specific account>",
      "timeframe": "<e.g. Weeks 1-2>",
      "impact": "high|medium|low"
    }
  ],
  "totalProjectedOpportunity": <sum of all quantifiable revenue projections>,
  "ctaMessage": "<2-3 sentences, personalised to their actual numbers, creating urgency without being salesy. Reference the total opportunity found and what a strategy call would cover.>"
}`;

// ─── Main Route ──────────────────────────────────────────────────────────────

app.post('/analyse', upload.array('reports', 10), async (req, res) => {
  try {
    const { accountName, name, email, phone } = req.body;

    if (!req.files || req.files.length === 0) {
      return res.status(400).json({ error: 'No files uploaded. Please upload at least the SP Search Term report.' });
    }

    if (!email || !name) {
      return res.status(400).json({ error: 'Name and email are required.' });
    }

    // Parse reports
    const reports = {};
    const uploadedTypes = [];

    for (const file of req.files) {
      const rows = normaliseHeaders(parseCSV(file.buffer));
      if (rows.length === 0) continue;
      const headers = Object.keys(rows[0]);
      const type = detectReportType(headers);
      reports[type] = rows;
      uploadedTypes.push(type);
    }

    // Aggregate each report
    const aggregated = {};
    if (reports.sp_search_term) aggregated.sp_search_term = aggregateSPSearchTerm(reports.sp_search_term);
    if (reports.budget) aggregated.budget = aggregateBudget(reports.budget);
    if (reports.placement) aggregated.placement = aggregatePlacement(reports.placement);
    if (reports.business_report) aggregated.business_report = aggregateBusinessReport(reports.business_report);
    if (reports.brand_analytics) aggregated.brand_analytics = aggregateBrandAnalytics(reports.brand_analytics);
    if (reports.repeat_purchase) aggregated.repeat_purchase = aggregateRepeatPurchase(reports.repeat_purchase);
    if (reports.targeting) aggregated.targeting = aggregateTargeting(reports.targeting);

    if (!aggregated.sp_search_term) {
      return res.status(400).json({ error: 'Could not detect SP Search Term report. Please check the file and try again.' });
    }

    const projections = calculateProjections(aggregated);

    const userMessage = `Analyse this Amazon advertising account and produce the full audit JSON.

Account name: ${accountName}
Period: Last 30 days
Reports uploaded: ${uploadedTypes.join(', ')}

AGGREGATED DATA:
${JSON.stringify({ aggregated, projections }, null, 2)}

Important: Reference specific numbers from this data. Do not be generic. Output JSON only.`;

    const claudeResponse = await anthropic.messages.create({
      model: 'claude-sonnet-4-6',
      max_tokens: 4000,
      system: SYSTEM_PROMPT,
      messages: [{ role: 'user', content: userMessage }]
    });

    let responseText = claudeResponse.content[0].text.trim();
    // Strip any accidental markdown fences
    responseText = responseText.replace(/^```(?:json)?\n?/i, '').replace(/\n?```$/i, '').trim();

    let auditData;
    try {
      auditData = JSON.parse(responseText);
    } catch (e) {
      // Try extracting JSON if there's surrounding text
      const match = responseText.match(/\{[\s\S]*\}/);
      if (match) {
        try { auditData = JSON.parse(match[0]); }
        catch (e2) { return res.status(500).json({ error: 'Failed to parse audit response. Please try again.' }); }
      } else {
        return res.status(500).json({ error: 'Unexpected response format. Please try again.' });
      }
    }

    // Fire HubSpot and Drive in background
    submitToHubSpot({ accountName, name, email, phone, auditScore: auditData.accountScore })
      .catch(err => console.error('HubSpot error:', err.message));

    saveToDrive({ accountName, name, email, files: req.files, auditData })
      .catch(err => console.error('Drive error:', err.message));

    res.json({ success: true, audit: auditData, accountName });

  } catch (error) {
    console.error('Analyse error:', error);
    res.status(500).json({ error: 'An error occurred during analysis. Please try again.' });
  }
});

// ─── HubSpot ─────────────────────────────────────────────────────────────────

async function submitToHubSpot({ accountName, name, email, phone, auditScore }) {
  if (!process.env.HUBSPOT_ACCESS_TOKEN) return;

  const nameParts = name.trim().split(' ');
  const firstname = nameParts[0];
  const lastname = nameParts.slice(1).join(' ') || '';

  try {
    // Try to create contact; if duplicate, update by email
    await axios.post(
      'https://api.hubapi.com/crm/v3/objects/contacts',
      {
        properties: {
          firstname,
          lastname,
          email,
          phone,
          company: accountName,
          hs_lead_source: 'Amazon Audit Tool',
          amazon_audit_score: auditScore?.toString() || ''
        }
      },
      {
        headers: {
          Authorization: `Bearer ${process.env.HUBSPOT_ACCESS_TOKEN}`,
          'Content-Type': 'application/json'
        }
      }
    );
  } catch (err) {
    if (err.response?.status === 409) {
      // Contact exists — update instead
      const existing = err.response.data?.message?.match(/ID: (\d+)/)?.[1];
      if (existing) {
        await axios.patch(
          `https://api.hubapi.com/crm/v3/objects/contacts/${existing}`,
          { properties: { amazon_audit_score: auditScore?.toString(), company: accountName } },
          { headers: { Authorization: `Bearer ${process.env.HUBSPOT_ACCESS_TOKEN}`, 'Content-Type': 'application/json' } }
        );
      }
    } else throw err;
  }
}


// ─── Google Drive ─────────────────────────────────────────────────────────────

function getDriveClient() {
  if (!process.env.GOOGLE_SERVICE_ACCOUNT_JSON) return null;
  try {
    const creds = JSON.parse(process.env.GOOGLE_SERVICE_ACCOUNT_JSON);
    const auth = new google.auth.GoogleAuth({
      credentials: creds,
      scopes: ['https://www.googleapis.com/auth/drive']
    });
    return google.drive({ version: 'v3', auth });
  } catch (e) {
    console.error('Drive auth error:', e.message);
    return null;
  }
}

async function createDriveFolder(drive, name, parentId) {
  const res = await drive.files.create({
    requestBody: {
      name,
      mimeType: 'application/vnd.google-apps.folder',
      parents: [parentId]
    },
    fields: 'id'
  });
  return res.data.id;
}

async function uploadFileToDrive(drive, folderId, filename, buffer, mimeType) {
  const stream = Readable.from(buffer);
  await drive.files.create({
    requestBody: {
      name: filename,
      parents: [folderId]
    },
    media: {
      mimeType: mimeType || 'application/octet-stream',
      body: stream
    }
  });
}

async function saveToDrive({ accountName, name, email, files, auditData }) {
  const drive = getDriveClient();
  const parentFolderId = process.env.GOOGLE_DRIVE_FOLDER_ID;
  if (!drive || !parentFolderId) return;

  try {
    const date = new Date().toISOString().slice(0, 10);
    const folderName = `${accountName} — ${date}`;
    const folderId = await createDriveFolder(drive, folderName, parentFolderId);

    // Upload raw report files
    for (const file of files) {
      const ext = file.originalname.split('.').pop().toLowerCase();
      const mime = ext === 'csv' ? 'text/csv'
        : ext === 'xlsx' ? 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet'
        : 'application/octet-stream';
      await uploadFileToDrive(drive, folderId, file.originalname, file.buffer, mime);
    }

    // Upload audit JSON summary
    const summary = {
      submittedAt: new Date().toISOString(),
      accountName,
      contactName: name,
      contactEmail: email,
      accountScore: auditData.accountScore,
      totalOpportunity: auditData.totalProjectedOpportunity,
      headline: auditData.headline,
      audit: auditData
    };
    const summaryBuffer = Buffer.from(JSON.stringify(summary, null, 2));
    await uploadFileToDrive(drive, folderId, 'audit-summary.json', summaryBuffer, 'application/json');

    console.log(`Drive: saved ${files.length} files + summary to "${folderName}"`);
  } catch (e) {
    console.error('Drive upload error:', e.message);
  }
}

app.get('/health', (req, res) => res.json({ status: 'ok', timestamp: new Date().toISOString() }));

const PORT = process.env.PORT || 3000;
app.listen(PORT, () => console.log(`Amazon Audit Tool backend running on port ${PORT}`));
