-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColorPreparation.carryLibrary_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:03:41.207321+00:00
-- url     : https://prove2.me/submissions/3e47c057-a3cf-49bf-840d-5071e3f6a1c5

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
theorem _root_.solution : carryLibrary.length=42 := rfl
end ThreeSum.LightWeightedGlobalColorPreparation
