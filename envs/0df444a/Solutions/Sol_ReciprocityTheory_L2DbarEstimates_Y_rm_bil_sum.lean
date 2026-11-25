-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rm_bil_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:26:06.487294+00:00
-- url     : https://prove2.me/submissions/5d49689a-b153-494e-bae4-8e74ceed2c68

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (B : V n →L[ℝ] V n →L[ℝ] ℝ) (c : Fin n → ℂ) :
    B (∑ j, c j • bas n j) (∑ k, c k • bas n k) = ∑ j, ∑ k, B (c j • bas n j) (c k • bas n k) := by
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_comm
end ReciprocityTheory.L2DbarEstimates.Y
