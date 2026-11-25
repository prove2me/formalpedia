-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.differentiable_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:08.910223+00:00
-- url     : https://prove2.me/submissions/d7c759e8-cf44-480a-a0dd-4fd3a80e88fe

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_EuclideanAtlasPointwiseNormSqUnitSection
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_hasFDerivAt_coord

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
theorem _root_.solution (m : Fin n) : Differentiable ℂ (fun v : V n => v m) := fun y => (hasFDerivAt_coord m y).differentiableAt
end ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
