-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredQueryBudget.query_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:33:30.825008+00:00
-- url     : https://prove2.me/submissions/93358fbc-4b1f-47a8-80fe-21e32d0a3dcc

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredQueryBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCountFrontendBudget_envelope_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalUniformQueryTime_allocated_word
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalUniformQueryTime_maximum_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedQueryBudget_envelope_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredQueryBudget
open WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaSourceSetup
open WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredQueryBudget
theorem _root_.solution (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hn : 1<n) (hA : A.length≤n) (hB : B.length≤n) (hC : C.length≤n) :
    (queryTime P n free A B C:ℝ)≤
      (coefficient P:ℝ)*(J P n+1:ℕ)^3*
        WeightedGlobalCountFrontendBudget.envelope P.m (rounds P n) := by
  have hword : ∀j≤WeightedGlobalCoverScale.radixLength P.m n,
      WeightedGlobalFrontendResources.eulerBound (N P.m j)
        (valueCap (r:=j) P.maps P.cap (baseInput P n free A B C))≤
      (256*(P.allocation.D+1))*(n+n^κ+1)^P.allocation.E := by
    intro j hj
    exact WeightedGlobalUniformQueryTime.allocated_word P.maps P.allocation (baseInput P n free A B C)
      hj hB hC (Nat.mul_le_mul_right _ hA) (le_refl _)
  have hh := WeightedGlobalUniformQueryTime.maximum_bound P.maps P.cap (baseInput P n free A B C)
    P.blockPositive hn (le_refl (n^κ)) hword
  change (queryTime P n free A B C:ℝ)≤
    (coefficient P:ℝ)*(WeightedGlobalCoverScale.radixLength P.m n+1:ℕ)^3*
      WeightedGlobalCountFrontendBudget.envelope P.m (rounds P n) at hh
  apply hh.trans
  have hr : WeightedGlobalCoverScale.radixLength P.m n≤J P n := by
    unfold J LightWeightedGlobalDimensions.J WeightedGlobalSignedPadding.paddedLength LightWeightedGlobalDimensions.r Profile.M
    unfold WeightedGlobalCoverScale.radixLength
    omega
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) 3)
      (Nat.cast_nonneg _)) (WeightedGlobalCountFrontendBudget.envelope_pos _ _).le
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredQueryBudget
