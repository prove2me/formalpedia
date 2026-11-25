-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_phase_bound_e8e64de5478d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:27.452077+00:00
-- url     : https://prove2.me/submissions/53cf61d8-0fa6-4382-a116-bbec7f380d6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_smul_d6bde57d50a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_differentiable_eval_line_1108a13d8f8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_log_norm_le_circleAverage_d54a5c877eaa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_integral_phaseLaw_dd825db4ed22

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
theorem _root_.solution {Q : MvPolynomial (Fin N) ℂ} {d : ℕ} (hQ : Q.IsHomogeneous d)
    (p t : Fin N → ℂ) (hp : eval p Q ≠ 0) {r : ℝ} (hr : 0 < r) (b : ℝ) :
    Real.log ‖eval p Q‖ + d * Real.log r ≤
      ∫ θ, Real.log ‖eval (((r : ℂ) * Complex.exp (θ * Complex.I)) • p + (b : ℂ) • t) Q‖ ∂phaseLaw := by
  set g : ℂ → ℂ := fun w => eval ((r : ℂ) • p + w • ((b : ℂ) • t)) Q with hg
  have hgd : Differentiable ℂ g := differentiable_eval_line Q _ _
  have hg0 : g 0 = (r : ℂ) ^ d * eval p Q := by
    simp only [hg, zero_smul, add_zero]
    exact eval_smul hQ _ _
  have hg0' : g 0 ≠ 0 := by
    rw [hg0]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hr.ne')) hp
  have hlog0 : Real.log ‖g 0‖ = Real.log ‖eval p Q‖ + d * Real.log r := by
    rw [hg0, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.log_mul (pow_ne_zero _ hr.ne') (norm_ne_zero_iff.mpr hp), Real.log_pow]
    ring

  have hpt : ∀ θ : ℝ, Real.log ‖eval (((r : ℂ) * Complex.exp (θ * Complex.I)) • p + (b : ℂ) • t) Q‖ =
      Real.log ‖g (circleMap 0 1 (-θ))‖ := by
    intro θ
    have he : Complex.exp (θ * Complex.I) * Complex.exp ((-θ : ℝ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      push_cast
      simp
    have hv : ((r : ℂ) * Complex.exp (θ * Complex.I)) • p + (b : ℂ) • t =
        Complex.exp (θ * Complex.I) • ((r : ℂ) • p + Complex.exp ((-θ : ℝ) * Complex.I) • ((b : ℂ) • t)) := by
      rw [smul_add, smul_smul, smul_smul, smul_smul, he, one_mul, mul_comm (r : ℂ)]
    rw [hv, eval_smul hQ, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow, one_mul]
    simp [hg, circleMap]
  have hper : Function.Periodic (fun θ => Real.log ‖g (circleMap 0 1 θ)‖) (2 * π) :=
    (periodic_circleMap 0 1).comp (fun z => Real.log ‖g z‖)
  have hint : ∫ θ in -π..π, Real.log ‖g (circleMap 0 1 (-θ))‖ =
      ∫ θ in (0 : ℝ)..2 * π, Real.log ‖g (circleMap 0 1 θ)‖ := by
    rw [intervalIntegral.integral_comp_neg (fun θ => Real.log ‖g (circleMap 0 1 θ)‖), neg_neg]
    have := hper.intervalIntegral_add_eq (-π) 0
    rwa [show -π + 2 * π = π by ring, zero_add] at this
  rw [← hlog0, integral_phaseLaw]
  simp_rw [hpt]
  rw [hint]
  have hJ := log_norm_le_circleAverage hgd hg0'
  rwa [circleAverage_def, smul_eq_mul] at hJ
end GroundTheory.Heights₂.Heights.PointwiseLelong
