-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:03.693039+00:00
-- url     : https://prove2.me/submissions/d9e77058-ed08-43b8-9e4a-7a0fe0a48a09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pow_mul_exp_neg_mul_sq_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integrable_exp_neg_mul_norm_sq_euclidean

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
theorem _root_.solution {g : ℕ} (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)) := by
  have hb2 : 0 < b / 2 := by positivity
  refine ((integrable_exp_neg_mul_norm_sq_euclidean (g := g) hb2).const_mul (1 + n.factorial * (2 / b) ^ n)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_mul_exp_neg_mul_sq_le n hb (norm_nonneg z)
end ReciprocityTheory.ChartRestriction.G.I2
