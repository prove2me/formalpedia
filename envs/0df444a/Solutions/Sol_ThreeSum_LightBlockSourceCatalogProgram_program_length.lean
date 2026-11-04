-- Prove2me | solution 1 for ThreeSum.LightBlockSourceCatalogProgram.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:57:10.518004+00:00
-- url     : https://prove2.me/submissions/33ee04d9-bb6b-4836-a714-35879f8b4e24

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchProgram
import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceCatalogProgram
open Light SubsetAddress LightBlockSourceCatalog
set_option maxHeartbeats 2200000
set_option maxRecDepth 16000
namespace ThreeSum.LightBlockSourceCatalogProgram
theorem _root_.solution : program.length = 47 := rfl
end ThreeSum.LightBlockSourceCatalogProgram
