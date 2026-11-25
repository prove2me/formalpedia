-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integral_monomialKernel_mul_gaussian_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:45.12352+00:00
-- url     : https://prove2.me/submissions/aebec8d2-5626-4e93-8a35-117fbd2dc22c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_monomialMass_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_norm_monomial_sq_gaussian_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integrable_norm_monomial_sq_gaussian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_norm_monomial_sq_gaussian_half


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
theorem _root_.solution {g : ℕ} (p : MvPolynomial (Fin g) ℂ) :
    ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      Real.pi ^ g * ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) := by
  simp only [fa1K, Finset.sum_mul]
  rw [integral_finsetSum _ (fun α _ => ?_)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    have : ∀ z : EuclideanSpace ℂ (Fin g),
        ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
        (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := fun z => by ring
    simp only [this]
    rw [integral_const_mul, integral_norm_monomial_sq_gaussian_half, integral_norm_monomial_sq_gaussian_eq]
    have := (monomialMass_pos α).ne'
    field_simp
  · have := (integrable_norm_monomial_sq_gaussian α (b := 1 / 2) (by norm_num)).const_mul (fa1M α)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only; ring
end ReciprocityTheory.ChartRestriction.G.I2
