-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integral_monomialKernel_mul_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:39.958068+00:00
-- url     : https://prove2.me/submissions/937231ba-6a0c-4fb3-af08-bbce2035222b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_monomialMass_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_norm_monomial_sq_gaussian_eq

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
    ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-‖z‖ ^ 2) = Real.pi ^ g * p.support.card := by
  have hint : ∀ α : Fin g →₀ ℕ,
      MeasureTheory.Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    intro α
    by_contra h
    apply (monomialMass_pos α).ne'
    unfold fa1M
    rw [MeasureTheory.integral_undef h, mul_zero]
  unfold fa1K
  have hfun : (fun z : EuclideanSpace ℂ (Fin g) =>
      (∑ α ∈ p.support, ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α) * Real.exp (-‖z‖ ^ 2)) =
      fun z => ∑ α ∈ p.support, (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    funext z
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  rw [hfun, MeasureTheory.integral_finset_sum _ (fun α _ => (hint α).const_mul _)]
  have h2 : ∀ α ∈ p.support,
      ∫ z, (fa1M α)⁻¹ * (‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) = Real.pi ^ g := by
    intro α _
    rw [MeasureTheory.integral_const_mul, integral_norm_monomial_sq_gaussian_eq, mul_comm (Real.pi ^ g), ← mul_assoc,
      inv_mul_cancel₀ (monomialMass_pos α).ne', one_mul]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.I2
