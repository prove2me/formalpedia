-- Prove2me | solution 1 for ThreeSum.SharedReportingCosts.shared_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:14:37.991193+00:00
-- url     : https://prove2.me/submissions/7cad5023-8004-40a6-bb59-9da3830c3119

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingCosts
import Theorems.Thm_ThreeSum_SharedReportingCosts_levels_time_le

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingCosts
open Scales CostLedger ReportingHostPrefixCatalog
set_option maxHeartbeats 1700000
set_option maxRecDepth 10000
namespace ThreeSum.SharedReportingCosts
theorem _root_.solution (n : ℕ) : sharedTime n ≤ budget n := by
  have hh := Nat.mul_le_mul_left
    (3*CostLedger.bandCount n^2*TrimScales.scheduleCount n) (levels_time_le n)
  unfold sharedTime budget StageBounds.boxCount
  convert hh using 1 <;> ring
end ThreeSum.SharedReportingCosts
