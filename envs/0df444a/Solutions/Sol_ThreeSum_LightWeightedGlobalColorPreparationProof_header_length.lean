-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalColorPreparationProof.header_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:18:35.575989+00:00
-- url     : https://prove2.me/submissions/3005d136-c937-4c53-815b-49c85894a955

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalColorPreparationProof
open Light LightWeightedGlobalColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedGlobalColorPreparationProof
theorem _root_.solution (free n U R J q menu : ℕ) (A B C : List ℤ) :
    (header free n U R J q menu A B C).length=19 :=rfl
end ThreeSum.LightWeightedGlobalColorPreparationProof
