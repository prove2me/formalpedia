-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.exp_neg_ph_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:57:26.478639+00:00
-- url     : https://prove2.me/submissions/13ebedb1-6a16-4207-a3b1-fe47af8355e3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_EuclideanAtlasPointwiseNormSqUnitSection
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_ph_one

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
theorem _root_.solution (y : V n) : Real.exp (-(atlas n).ph 1 () y) = (1 + ‖y‖ ^ 2)⁻¹ := by
  rw [ph_one, Real.exp_neg, Real.exp_log (pos_one_add y)]
end ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
