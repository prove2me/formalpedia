-- Prove2me | solution 1 for ThreeSum.LightReportingSortedCatalog.procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:47.202005+00:00
-- url     : https://prove2.me/submissions/2768cecc-f97a-4d07-abc3-1846b73c51b2

import Definitions.Def_Submission_ThreeSum_LightReportingPackKeys
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSortedCatalog
open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog
variable {lim : Limits}
namespace ThreeSum.LightReportingSortedCatalog
theorem _root_.solution : MergeSort.Procs program 2 3 4 5 := ⟨rfl,rfl,rfl,rfl⟩
end ThreeSum.LightReportingSortedCatalog
