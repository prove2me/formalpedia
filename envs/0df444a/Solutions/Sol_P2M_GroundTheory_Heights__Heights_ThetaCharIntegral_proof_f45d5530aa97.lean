-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ThetaCharIntegral_proof_f45d5530aa97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:59.787515+00:00
-- url     : https://prove2.me/submissions/9f08d830-dcd5-4c56-a64f-b7c59f3e409d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaCharIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_integral_Icc_exp_b28c0fec4769
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_torusChar_eq_prod_1de5f9bae33f

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
open Real MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ThetaCharIntegral
theorem _root_.solution : ThetaCharIntegral.Statement := by
  intro g m
  have hset : Set.Icc (0 : Fin g → ℝ) 1 = Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 := by
    rw [← Set.pi_univ_Icc]; rfl
  rw [hset, volume_pi, Measure.restrict_pi_pi]
  simp_rw [KThetaCharIntegral.torusChar_eq_prod]
  rw [integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (t : ℂ))))]
  simp_rw [KThetaCharIntegral.integral_Icc_exp]
  by_cases hm : m = 0
  · subst hm; simp
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (funext h)
    rw [if_neg hm]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
end ThetaCharIntegral
end GroundTheory.Heights₂.Heights
