-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColorPreparation.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:54:26.571771+00:00
-- url     : https://prove2.me/submissions/9d451791-d11f-406a-ab11-41ba1e91c766

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
theorem _root_.solution (radix : ℕ) : (program radix).length=51 := rfl
end ThreeSum.LightWeightedGlobalColorPreparation
