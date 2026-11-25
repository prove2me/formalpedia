-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_Y_abs_rmRho__le_1a70138217c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:29.814906+00:00
-- url     : https://prove2.me/submissions/9a608176-dcfa-436c-ba09-a39495c16d4e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_abs_rmStep_le

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
theorem _root_.solution (t : ℝ) : |rmRho' t| ≤ 1 := by
  have h1 := abs_le.mp (abs_rmStep_le t)
  have h2 := abs_le.mp (abs_rmStep_le (-t))
  unfold rmRho'
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
end ReciprocityTheory.L2DbarEstimates.Y
