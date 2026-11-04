-- Prove2me | solution 1 for ThreeSum.SharedReportingCosts.prefix_count_le_boxes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:25:42.898275+00:00
-- url     : https://prove2.me/submissions/a3ed2810-401d-45f5-88b4-77c89618dbc8

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingCosts
import Theorems.Thm_ThreeSum_SharedReportingCosts_prefix_count_eq
import Theorems.Thm_ThreeSum_CostLedger_suffixBoxes_pos


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingCosts
open Scales CostLedger ReportingHostPrefixCatalog
set_option maxHeartbeats 1700000
set_option maxRecDepth 10000
namespace ThreeSum.SharedReportingCosts
theorem _root_.solution (n k : ℕ) :
    LightReportingPrefixCatalog.count (half n) k ≤ prefixBoxes n k := by
  rw [prefix_count_eq]
  exact Nat.le_mul_of_pos_right _ (suffixBoxes_pos n k)
end ThreeSum.SharedReportingCosts
