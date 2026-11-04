-- Prove2me | solution 1 for ThreeSum.LightReportingCatalogLookup.word_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:01.1102+00:00
-- url     : https://prove2.me/submissions/bc37c788-a7c7-458b-82bd-27e5efbf41da

import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingCatalogLookup
open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
variable {lim : Limits}
namespace ThreeSum.LightReportingCatalogLookup
theorem _root_.solution (U n A B : ℕ) :
    U ≤ 4*U+4*(n+1)+n+A+B+16 ∧ A ≤ 4*U+4*(n+1)+n+A+B+16 ∧
    n+A+16 ≤ 4*U+4*(n+1)+n+A+B+16 ∧ 4*U+4*(n+1)+16 ≤ 4*U+4*(n+1)+n+A+B+16 := by omega
end ThreeSum.LightReportingCatalogLookup
