-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColorPreparation.leftLibrary_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:57:10.478215+00:00
-- url     : https://prove2.me/submissions/e472d29e-bcf7-4805-91a5-6f549fe4417c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPrelude
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalColorPreparation
open Light
set_option maxRecDepth 20000
namespace ThreeSum.LightWeightedGlobalColorPreparation
theorem _root_.solution : leftLibrary.length=32 := rfl
end ThreeSum.LightWeightedGlobalColorPreparation
