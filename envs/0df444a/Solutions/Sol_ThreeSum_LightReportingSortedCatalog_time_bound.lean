-- Prove2me | solution 1 for ThreeSum.LightReportingSortedCatalog.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:05:39.950625+00:00
-- url     : https://prove2.me/submissions/ab21b5e9-5d3e-449c-884d-1aaf8c04cd7a

import Definitions.Def_Submission_ThreeSum_LightReportingPackKeys
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSortedCatalog
open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog
variable {lim : Limits}
namespace ThreeSum.LightReportingSortedCatalog
theorem _root_.solution (W n : ℕ) : time W n ≤ 200*(W+1)+200*(n+1)*(Nat.clog 2 n+1) := by
  unfold time powTableTime LightReportingPackKeys.time sortTime
  have hh : n-1 ≤ n := Nat.sub_le _ _
  nlinarith
end ThreeSum.LightReportingSortedCatalog
