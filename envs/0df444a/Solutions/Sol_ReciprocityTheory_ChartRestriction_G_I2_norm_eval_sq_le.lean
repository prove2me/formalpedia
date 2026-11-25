-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.norm_eval_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:56.650383+00:00
-- url     : https://prove2.me/submissions/ccdf80e4-0ac3-454f-9b03-a1445d77bb5d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_monomialMass_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_eval_eq_sum_coeff_mul_monomial

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
theorem _root_.solution {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    ‖MvPolynomial.eval (fun i => z i) p‖ ^ 2 ≤ fa1N p * fa1K p z := by
  rw [eval_eq_sum_coeff_mul_monomial]
  have hM : ∀ α : Fin g →₀ ℕ, 0 < fa1M α := monomialMass_pos
  have h1 : ‖∑ α ∈ p.support, MvPolynomial.coeff α p * monomialOfMultiindex α z‖ ≤
      ∑ α ∈ p.support, (‖MvPolynomial.coeff α p‖ * Real.sqrt (fa1M α)) *
        (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α)) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun α _ => ?_))
    have hs : Real.sqrt (fa1M α) ≠ 0 := (Real.sqrt_pos.mpr (hM α)).ne'
    rw [norm_mul]
    first
    | (field_simp; done)
    | (field_simp; ring)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq p.support
    (fun α => ‖MvPolynomial.coeff α p‖ * Real.sqrt (fa1M α)) (fun α => ‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α))
  have h3 : ∀ α, (‖MvPolynomial.coeff α p‖ * Real.sqrt (fa1M α)) ^ 2 = ‖MvPolynomial.coeff α p‖ ^ 2 * fa1M α :=
    fun α => by rw [mul_pow, Real.sq_sqrt (hM α).le]
  have h4 : ∀ α, (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α)) ^ 2 = ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α :=
    fun α => by rw [div_pow, Real.sq_sqrt (hM α).le]
  simp only [h3, h4] at h2
  unfold fa1N fa1K
  calc _ ≤ (∑ α ∈ p.support, (‖MvPolynomial.coeff α p‖ * Real.sqrt (fa1M α)) *
        (‖monomialOfMultiindex α z‖ / Real.sqrt (fa1M α))) ^ 2 := by gcongr
    _ ≤ _ := h2
end ReciprocityTheory.ChartRestriction.G.I2
