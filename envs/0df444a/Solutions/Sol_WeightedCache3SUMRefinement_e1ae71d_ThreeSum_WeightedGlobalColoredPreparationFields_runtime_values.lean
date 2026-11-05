-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationFields.runtime_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:20:11.686034+00:00
-- url     : https://prove2.me/submissions/b2a87f99-b324-47e9-9b48-3949a10151d4

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColoredInitializationProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredPreparationFields

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationFields
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationFields
theorem _root_.solution (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) :
    LightWeightedGlobalColoredInitializationProof.runtimeValues n P.p (4^WeightedGlobalLocalParameters.fixedLength P.m) P.F
      (field P n free menu A B C)=
      LightWeightedGlobalColoredInitializationProof.values n (n^κ) (input P n free A B C).free
        (arrays P n free menu A B C).Bmatrix B.length (arrays P n free menu A B C).Cmatrix C.length
        (arrays P n free menu A B C).Omatrix (A.length*2^(J P n))
        (arrays P n free menu A B C).positions menu (J P n) P.p (4^WeightedGlobalLocalParameters.fixedLength P.m) P.F (q P n) := by
  rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredPreparationFields
