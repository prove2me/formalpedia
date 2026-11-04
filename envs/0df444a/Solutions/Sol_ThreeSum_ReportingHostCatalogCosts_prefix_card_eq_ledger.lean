-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogCosts.prefix_card_eq_ledger
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:06.718206+00:00
-- url     : https://prove2.me/submissions/c9af5e81-5cda-4a62-90dd-9190e273c408

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_prefix_card


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogCosts
set_option maxRecDepth 8000
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open ReportingHostPrefixCatalog ReportingHostSuffixCosts
namespace ThreeSum.ReportingHostCatalogCosts
theorem _root_.solution {n h k : ℕ} (hsize : 2*h = Scales.muZero n) :
    Fintype.card (Prefix h k) = CostLedger.prefixChoices n k := by
  have hhalf : Scales.muZero n/2 = h := by omega
  have hwidth : 512*h = 256*Scales.muZero n := by omega
  rw [prefix_card,CostLedger.prefixChoices,CostLedger.microOutputs,CostLedger.microPartitions,
    hwidth,hsize,hhalf]
end ThreeSum.ReportingHostCatalogCosts
