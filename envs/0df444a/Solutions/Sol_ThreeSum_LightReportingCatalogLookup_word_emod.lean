-- Prove2me | solution 1 for ThreeSum.LightReportingCatalogLookup.word_emod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:14:28.659459+00:00
-- url     : https://prove2.me/submissions/fceb0c50-62dc-4a5e-ab01-c0388180efdb

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
theorem _root_.solution (W n : ℕ) : 4*valueBound W n+4*(n+1)+16 ≤ word W n := (word_components _ _ _ _).2.2.2
end ThreeSum.LightReportingCatalogLookup
