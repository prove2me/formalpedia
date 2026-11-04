-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredPreparationFields.header_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:32:23.719513+00:00
-- url     : https://prove2.me/submissions/10b021c0-5eaa-4248-806f-13d2838e897a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredInitializationProof
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationFields

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPreparationFields
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredPreparationFields
theorem _root_.solution (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) :
    LightWeightedGlobalColorPreparationProof.header free n (n^κ) (rounds P n) (J P n) (q P n) menu A B C=
      (fields P n free menu A B C).map (fun i=>(i:ℤ)) := rfl
end ThreeSum.WeightedGlobalColoredPreparationFields
