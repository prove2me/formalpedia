-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:55.688843+00:00
-- url     : https://prove2.me/submissions/baa18efb-7634-4b1a-b2c2-1898f769ca2b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_EuclideanAtlasPointwiseNormSqUnitSection
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_zLoc_eq

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
theorem _root_.solution (y : V n) :
    (fderiv ℂ ((atlas n).zLoc (w0I n) (sI n) ((atlas n).pick y))
      ((atlas n).chart ((atlas n).pick y) y)).det ≠ 0 := by
  rw [zLoc_eq, fderiv_id]
  show LinearMap.det (LinearMap.id : V n →ₗ[ℂ] V n) ≠ 0
  rw [LinearMap.det_id]
  exact one_ne_zero
end ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
