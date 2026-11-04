-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogCosts.prefix_card_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:37.873193+00:00
-- url     : https://prove2.me/submissions/67b03e5c-413d-4194-94f7-48dc7809f7d2

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
theorem _root_.solution (h k : ℕ) : 0 < Fintype.card (Prefix h k) := by
  rw [prefix_card]
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))
end ThreeSum.ReportingHostCatalogCosts
