-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_ne_zero_of_max_d14cb858f69d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:35.157934+00:00
-- url     : https://prove2.me/submissions/52d8e283-d034-4bbd-8edf-7cb10e1cd3e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_smul_d6bde57d50a9

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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}
namespace GroundTheory.Heights₂.Heights.PointwiseLelong
theorem _root_.solution {d : ℕ} {Q : MvPolynomial (Fin N) ℂ} (hQ0 : Q ≠ 0)
    (hQ : Q.IsHomogeneous d) {p : Fin N → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hmax : ∀ z : Fin N → ℂ, ∑ j, ‖z j‖ ^ 2 = 1 → ‖eval z Q‖ ≤ ‖eval p Q‖) : eval p Q ≠ 0 := by
  intro hzero
  have hS : ∀ z : Fin N → ℂ, ∑ j, ‖z j‖ ^ 2 = 1 → eval z Q = 0 := fun z hz => by
    have := hmax z hz
    rw [hzero, norm_zero] at this
    exact norm_le_zero_iff.mp this
  apply hQ0
  apply hQ.eq_zero_of_forall_eval_eq_zero
  intro x
  by_cases hx : x = 0
  · subst hx
    have := eval_smul hQ 0 p
    rw [zero_smul, hS p hp, mul_zero] at this
    exact this
  · have hT : 0 < ∑ j, ‖x j‖ ^ 2 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
      exact Finset.sum_pos' (fun i _ => sq_nonneg _)
        ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr (by simpa using hj)) 2⟩
    have hρ : 0 < √(∑ j, ‖x j‖ ^ 2) := Real.sqrt_pos.mpr hT
    have hsq : √(∑ j, ‖x j‖ ^ 2) ^ 2 = ∑ j, ‖x j‖ ^ 2 := Real.sq_sqrt hT.le
    have hs : ∑ j, ‖((((√(∑ i, ‖x i‖ ^ 2))⁻¹ : ℝ) : ℂ) • x) j‖ ^ 2 = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, mul_pow,
        ← Finset.mul_sum]
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hρ.le), inv_pow, hsq, inv_mul_cancel₀ hT.ne']
    have hxe : x = ((√(∑ j, ‖x j‖ ^ 2) : ℝ) : ℂ) • ((((√(∑ j, ‖x j‖ ^ 2))⁻¹ : ℝ) : ℂ) • x) := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hρ.ne', Complex.ofReal_one, one_smul]
    rw [hxe, eval_smul hQ, hS _ hs, mul_zero]
end GroundTheory.Heights₂.Heights.PointwiseLelong
