-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.nsq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:09:42.653846+00:00
-- url     : https://prove2.me/submissions/a051d6d0-5f3e-4534-a40c-1b17dfa464d7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_EuclideanAtlasPointwiseNormSqUnitSection
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_exp_neg_ph_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
theorem _root_.solution (f : Unit → V n → ℂ) (y : V n) :
    (atlas n).nsq 1 f y = ‖f () y‖ ^ 2 * (1 + ‖y‖ ^ 2)⁻¹ := by
  show ‖f () y‖ ^ 2 * Real.exp (-(atlas n).ph 1 () y) = _
  rw [exp_neg_ph_one]
end ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
