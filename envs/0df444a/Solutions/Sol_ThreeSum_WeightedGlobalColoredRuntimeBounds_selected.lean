-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredRuntimeBounds.selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T03:01:43.225741+00:00
-- url     : https://prove2.me/submissions/91aa71d0-c9d8-40e0-b745-ede2db44d701

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedCollisions
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Definitions.Def_Submission_Weighted_Global_TernaryColoredRuntimeBounds
import Theorems.Thm_ThreeSum_WeightedGlobalColoredRuntimeBounds_zero_native
import Theorems.Thm_ThreeSum_BandPartition_length_le
import Theorems.Thm_ThreeSum_BandWeightedScore_length_le
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_length_le
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_length_le
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans


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
    (H : (TernarySignedReduction.Coordinate (J P n)→ZMod P.p)→ₗ[ZMod P.p] (Fin j→ZMod P.p))
    (valuesA valuesB valuesC : ℕ→ℤ) (keysB keysC : ℕ→ℕ)
    (hj : j≤rounds P n) (hA : A.length≤n) (hB : B.length≤n) (hC : C.length≤n) :
    NativeBounds (k:=P.k) P.maps P.output
      (zeroInput (WeightedGlobalArenaPostSelection.selectedInput (input P n free A B C)
        (n^κ) P.radix A.length H valuesA valuesB valuesC keysB keysC))
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by
  apply zero_native P _ n j hj
  · exact (LightOriginalSurvivors.length_le keysB B.length).trans hB
  · exact (LightOriginalSurvivors.length_le keysC C.length).trans hC
  · exact Nat.mul_le_mul_right _ hA
  · exact le_rfl
end ThreeSum.WeightedGlobalColoredRuntimeBounds
