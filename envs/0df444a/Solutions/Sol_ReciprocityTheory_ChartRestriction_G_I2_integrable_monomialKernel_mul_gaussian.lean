-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integrable_monomialKernel_mul_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:38:29.209505+00:00
-- url     : https://prove2.me/submissions/84ba2fe0-44f8-4016-b04f-a48a4f0ab55e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integrable_norm_monomial_sq_gaussian


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
theorem _root_.solution {g : ℕ} (p : MvPolynomial (Fin g) ℂ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K p z * Real.exp (-b * ‖z‖ ^ 2)) := by
  simp only [fa1K, Finset.sum_mul]
  refine integrable_finsetSum _ (fun α _ => ?_)
  have := (integrable_norm_monomial_sq_gaussian α hb).const_mul (fa1M α)⁻¹
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only; ring
end ReciprocityTheory.ChartRestriction.G.I2
