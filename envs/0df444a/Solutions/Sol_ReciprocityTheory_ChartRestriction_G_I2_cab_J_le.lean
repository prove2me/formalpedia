-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_J_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:23:44.47685+00:00
-- url     : https://prove2.me/submissions/a830b05f-5a3c-414d-a478-20b419c43bea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cabPoly_eval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_Hf_norm_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_finrank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_gauss_integrable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (η : EuclideanSpace ℂ ι) (hη : ‖η‖ ≤ 1) (c q : ℕ) (hq : 1 ≤ q) :
    ∫ v : EuclideanSpace ℂ ι, ‖MvPolynomial.eval (fun i => v i) (cabPoly η c)‖ ^ 2 *
      Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤
      c.factorial * (2 / (q * Real.pi)) ^ c * (2 / q) ^ Fintype.card ι := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set s : ℝ := q * Real.pi / 2 with hs
  have hs0 : 0 < s := by positivity
  have hpt : ∀ v : EuclideanSpace ℂ ι, ‖MvPolynomial.eval (fun i => v i) (cabPoly η c)‖ ^ 2 *
      Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤
      (c.factorial * (2 / (q * Real.pi)) ^ c) * Real.exp (-s * ‖v‖ ^ 2) := by
    intro v
    rw [cabPoly_eval, norm_pow]
    have h1 : ‖Hf v η‖ ≤ ‖v‖ := (cab_Hf_norm_le v η).trans (mul_le_of_le_one_right (norm_nonneg _) hη)
    have h2 : (‖Hf v η‖ ^ c) ^ 2 ≤ (‖v‖ ^ 2) ^ c := by
      rw [← pow_mul, ← pow_mul, mul_comm]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 _
    have h3 : (s * ‖v‖ ^ 2) ^ c / c.factorial ≤ Real.exp (s * ‖v‖ ^ 2) :=
      Real.pow_div_factorial_le_exp (x := s * ‖v‖ ^ 2) (hx := by positivity) (n := c)
    have hf : (0 : ℝ) < c.factorial := by exact_mod_cast Nat.factorial_pos c
    have h4 : (‖v‖ ^ 2) ^ c ≤ c.factorial * (1 / s) ^ c * Real.exp (s * ‖v‖ ^ 2) := by
      rw [div_le_iff₀ hf, mul_pow] at h3
      have : (‖v‖ ^ 2) ^ c = (s ^ c * (‖v‖ ^ 2) ^ c) * (1 / s) ^ c := by
        rw [mul_comm (s ^ c), mul_assoc, ← mul_pow, mul_one_div_cancel hs0.ne', one_pow, mul_one]
      rw [this]
      have hp : 0 ≤ (1 / s) ^ c := by positivity
      calc s ^ c * (‖v‖ ^ 2) ^ c * (1 / s) ^ c ≤ Real.exp (s * ‖v‖ ^ 2) * c.factorial * (1 / s) ^ c :=
            mul_le_mul_of_nonneg_right h3 hp
        _ = _ := by ring
    have h5 : 1 / s = 2 / (q * Real.pi) := by rw [hs]; field_simp
    rw [h5] at h4
    have he : Real.exp (s * ‖v‖ ^ 2) * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) = Real.exp (-s * ‖v‖ ^ 2) := by
      rw [← Real.exp_add]; congr 1; rw [hs]; ring
    calc (‖Hf v η‖ ^ c) ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)
        ≤ (c.factorial * (2 / (q * Real.pi)) ^ c * Real.exp (s * ‖v‖ ^ 2)) *
          Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (h2.trans h4) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, he]
  have hint : Integrable (fun v : EuclideanSpace ℂ ι =>
      (c.factorial * (2 / (q * Real.pi)) ^ c) * Real.exp (-s * ‖v‖ ^ 2)) :=
    (pa_gauss_integrable hs0).const_mul _
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity) hint
    (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hs0, cab_finrank]
  congr 1
  have : Real.pi / s = 2 / q := by rw [hs]; field_simp
  rw [this]
  have : ((2 * Fintype.card ι : ℕ) : ℝ) / 2 = (Fintype.card ι : ℝ) := by push_cast; ring
  rw [this, Real.rpow_natCast]
end ReciprocityTheory.ChartRestriction.G.I2
