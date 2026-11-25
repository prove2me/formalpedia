-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.abs_rmStep_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:35.382821+00:00
-- url     : https://prove2.me/submissions/fab981f0-f0cd-4b73-9a04-c9c01408441f

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
theorem _root_.solution (t : ℝ) : |rmStep t| ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (t + 1 / 2)
  have h1 := Real.smoothTransition.le_one (t + 1 / 2)
  unfold rmStep
  rw [abs_le]
  constructor <;> linarith
end ReciprocityTheory.L2DbarEstimates.Y
