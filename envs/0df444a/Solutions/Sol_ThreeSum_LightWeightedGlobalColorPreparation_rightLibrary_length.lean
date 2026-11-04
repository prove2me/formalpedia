-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColorPreparation.rightLibrary_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:03:39.974123+00:00
-- url     : https://prove2.me/submissions/6c0320f6-aa55-4926-981f-76e10bcc2c3a

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
theorem _root_.solution : rightLibrary.length=36 := rfl
end ThreeSum.LightWeightedGlobalColorPreparation
