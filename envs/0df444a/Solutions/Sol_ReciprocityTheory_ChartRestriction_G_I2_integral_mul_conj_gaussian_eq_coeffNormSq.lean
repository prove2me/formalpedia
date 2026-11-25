-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integral_mul_conj_gaussian_eq_coeffNormSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:45:38.153839+00:00
-- url     : https://prove2.me/submissions/bfa72032-d46b-48e2-86bf-53593b9cce52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_norm_monomial_sq_gaussian_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_eval_eq_sum_coeff_mul_monomial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integrable_monomial_mul_conj_gaussian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_monomial_mul_conj_gaussian_eq_zero


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
theorem _root_.solution {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (F : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : ∀ z, F z = MvPolynomial.eval (fun i => z i) p) :
    (((Real.pi ^ g)⁻¹ : ℝ) : ℂ) * ∫ z, F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
      ((fa1N p : ℝ) : ℂ) := by
  have hexp : ∀ z, F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
      ∑ α ∈ p.support, ∑ β ∈ p.support,
        (MvPolynomial.coeff α p * (starRingEnd ℂ) (MvPolynomial.coeff β p)) *
          (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    intro z
    rw [hF, eval_eq_sum_coeff_mul_monomial, map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [map_mul]; ring
  simp only [hexp]
  have hint : ∀ α β : Fin g →₀ ℕ, Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      (MvPolynomial.coeff α p * (starRingEnd ℂ) (MvPolynomial.coeff β p)) *
        (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :=
    fun α β => (integrable_monomial_mul_conj_gaussian α β).const_mul _
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ => hint α β))]
  have hin : ∀ α ∈ p.support, ∫ z : EuclideanSpace ℂ (Fin g), ∑ β ∈ p.support,
      (MvPolynomial.coeff α p * (starRingEnd ℂ) (MvPolynomial.coeff β p)) *
        (monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) =
      (((‖MvPolynomial.coeff α p‖ ^ 2 * (Real.pi ^ g * fa1M α)) : ℝ) : ℂ) := by
    intro α hα
    rw [integral_finsetSum _ (fun β _ => hint α β)]
    rw [Finset.sum_eq_single_of_mem α hα (fun β _ hβ => by
      rw [integral_const_mul, integral_monomial_mul_conj_gaussian_eq_zero (Ne.symm hβ), mul_zero])]
    rw [integral_const_mul]
    have h1 : ∀ z : EuclideanSpace ℂ (Fin g),
        monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex α z) * (Real.exp (-‖z‖ ^ 2) : ℂ) =
          ((‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
      intro z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    simp only [h1]
    rw [integral_complex_ofReal, integral_norm_monomial_sq_gaussian_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [Finset.sum_congr rfl hin, fa1N]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have : (Real.pi : ℂ) ^ g ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  field_simp
end ReciprocityTheory.ChartRestriction.G.I2
