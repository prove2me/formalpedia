-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rmStep_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:25:52.546446+00:00
-- url     : https://prove2.me/submissions/797b86f4-1735-4ae4-b0ec-4b4fbd453702

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
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (t : ℝ) (h : t ≤ -1 / 2) : rmStep t = -1 := by
  unfold rmStep
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num
end ReciprocityTheory.L2DbarEstimates.Y
