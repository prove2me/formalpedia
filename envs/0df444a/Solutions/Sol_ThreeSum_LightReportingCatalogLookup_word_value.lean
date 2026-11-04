-- Prove2me | solution 1 for ThreeSum.LightReportingCatalogLookup.word_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:14:24.890088+00:00
-- url     : https://prove2.me/submissions/9e6a7373-c745-40ea-a5f1-2d4b66ee890f

import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Theorems.Thm_ThreeSum_LightReportingCatalogLookup_word_components

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingCatalogLookup
open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
variable {lim : Limits}
namespace ThreeSum.LightReportingCatalogLookup
theorem _root_.solution (W n : ℕ) : valueBound W n ≤ word W n := (word_components _ _ _ _).1
end ThreeSum.LightReportingCatalogLookup
