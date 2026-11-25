-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integral_norm_monomial_sq_gaussian_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:31.889949+00:00
-- url     : https://prove2.me/submissions/c7512bd6-f962-40f0-871d-5147d825d5d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {g : ℕ} (α : Fin g →₀ ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      2 ^ (g + ∑ i, α i) *
        ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpt : ∀ x : EuclideanSpace ℂ (Fin g),
      ‖monomialOfMultiindex α (Real.sqrt 2 • x)‖ ^ 2 * Real.exp (-(1 / 2) * ‖Real.sqrt 2 • x‖ ^ 2) =
        2 ^ (∑ i, α i) * (‖monomialOfMultiindex α x‖ ^ 2 * Real.exp (-‖x‖ ^ 2)) := by
    intro x
    rw [fa1Mono_smul, norm_mul, norm_pow, Complex.norm_real, norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_pow, mul_pow, ← pow_mul,
      mul_comm (∑ i, α i) 2, pow_mul, hs2, show -(1 / 2) * (2 * ‖x‖ ^ 2) = -‖x‖ ^ 2 by ring]
    ring
  have e1 : ∫ x : EuclideanSpace ℂ (Fin g),
      ‖monomialOfMultiindex α (Real.sqrt 2 • x)‖ ^ 2 * Real.exp (-(1 / 2) * ‖Real.sqrt 2 • x‖ ^ 2) =
        2 ^ (∑ i, α i) * ∫ x : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α x‖ ^ 2 * Real.exp (-‖x‖ ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hdim : |(Real.sqrt 2 ^ Module.finrank ℝ (EuclideanSpace ℂ (Fin g)))⁻¹| = ((2 : ℝ) ^ g)⁻¹ := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin, pow_mul, hs2,
      abs_of_pos (by positivity)]
  have e2 := MeasureTheory.Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℂ (Fin g)))
    (fun z => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) (Real.sqrt 2)
  beta_reduce at e2
  rw [hdim, smul_eq_mul, e1] at e2
  have h2g : (2 : ℝ) ^ g ≠ 0 := by positivity
  rw [pow_add, mul_assoc, e2, ← mul_assoc, mul_inv_cancel₀ h2g, one_mul]
end ReciprocityTheory.ChartRestriction.G.I2
