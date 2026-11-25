-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceLelongError_exists_bound_derivs_a1c87390a494
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:25.120959+00:00
-- url     : https://prove2.me/submissions/abe325c9-738e-436e-b76d-2afc339e73cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLelongError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceWeightBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBandEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLelongError
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_deriv_smoothTransition_eq_zero_da03c9a154fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_continuous_derivs_d2f475853b26
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_mem_Icc_57a0d0358e0c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.SliceLelongError
namespace GroundTheory.Heights₂.Heights.SliceLelongError
theorem _root_.solution : ∃ M₁ M₂ : ℝ, (∀ s, |deriv Real.smoothTransition s| ≤ M₁) ∧
    ∀ s, |deriv (deriv Real.smoothTransition) s| ≤ M₂ := by
  have hsupp : ∀ f : ℝ → ℝ, (∀ s, s < 0 ∨ 1 < s → f s = 0) → HasCompactSupport f := fun f hf =>
    HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun s hs => hf s (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs; exact hs)
  obtain ⟨M₁, hM₁⟩ := continuous_derivs.1.bounded_above_of_compact_support
    (hsupp _ fun s hs => (deriv_smoothTransition_eq_zero hs).1)
  obtain ⟨M₂, hM₂⟩ := continuous_derivs.2.bounded_above_of_compact_support
    (hsupp _ fun s hs => (deriv_smoothTransition_eq_zero hs).2)
  exact ⟨M₁, M₂, fun s => by simpa [Real.norm_eq_abs] using hM₁ s,
    fun s => by simpa [Real.norm_eq_abs] using hM₂ s⟩
end GroundTheory.Heights₂.Heights.SliceLelongError
