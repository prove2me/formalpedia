-- Prove2me | solution 1 for ThreeSum.SharedReportingCosts.prefix_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:18:53.296562+00:00
-- url     : https://prove2.me/submissions/9084c28a-a350-483d-81ca-0154d1b0af22

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingCosts
import Theorems.Thm_ThreeSum_ReportingHostCatalogCosts_prefix_card_eq_ledger
import Theorems.Thm_ThreeSum_ReportingHostPrefixCatalog_prefix_card


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingCosts
open Scales CostLedger ReportingHostPrefixCatalog
set_option maxHeartbeats 1700000
set_option maxRecDepth 10000
namespace ThreeSum.SharedReportingCosts
theorem _root_.solution (n k : ℕ) :
    LightReportingPrefixCatalog.count (half n) k=prefixChoices n k := by
  have hcard : LightReportingPrefixCatalog.count (half n) k=Fintype.card (Prefix (half n) k) := by
    rw [prefix_card]
    rfl
  exact hcard.trans (ReportingHostCatalogCosts.prefix_card_eq_ledger rfl)
end ThreeSum.SharedReportingCosts
