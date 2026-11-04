-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredPreparationFields.header_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:22:51.637236+00:00
-- url     : https://prove2.me/submissions/5b7b5b9e-5718-443e-be6b-4d0803955be1

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
theorem _root_.solution (P : Profile κ) (n free : ℕ) (A B C : List ℤ) :
    headerAt free n (LightColorParametersCosts.width n)+19≤(input P n free A B C).free := by
  change _≤arenaFree free n (LightColorParametersCosts.width n) A.length B.length C.length (J P n) (n^κ)
  unfold arenaFree work oMatrix positions carry cMatrix bMatrix
  omega
end ThreeSum.WeightedGlobalColoredPreparationFields
