-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integrable_of_norm_le_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:26:41.691803+00:00
-- url     : https://prove2.me/submissions/3b5ef22a-8c03-461f-87b0-23fc8d5c8171

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean

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
theorem _root_.solution {g : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : EuclideanSpace ℂ (Fin g) → E} (hf : Continuous f) (n : ℕ) {b C : ℝ} (hb : 0 < b)
    (h : ∀ z, ‖f z‖ ≤ C * (‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2))) : Integrable f := by
  exact ((integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean n hb).const_mul C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall h)
end ReciprocityTheory.ChartRestriction.G.I2
