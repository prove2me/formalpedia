-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredRuntimeBounds.base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:45:56.026199+00:00
-- url     : https://prove2.me/submissions/9590eda6-2cec-4656-9f5e-ebb42534f4ce

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeBounds_zero_native
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredRuntimeBounds
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory WeightedGlobalLocalParameters
open WeightedGlobalActualColoredRuntime
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredRuntimeBounds
theorem _root_.solution (P : Profile κ) (n free j : ℕ) (A B C : List ℤ)
    (hj : j≤rounds P n) (hA : A.length≤n) (hB : B.length≤n) (hC : C.length≤n) :
    NativeBounds (k:=P.k) P.maps P.output (zeroInput (input P n free A B C))
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by
  apply zero_native P _ n j hj hB hC (Nat.mul_le_mul_right _ hA) le_rfl
end ThreeSum.WeightedGlobalColoredRuntimeBounds
