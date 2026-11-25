-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_Y_rmRho__contDiff_ef760d6bef71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:59:37.375434+00:00
-- url     : https://prove2.me/submissions/ba9d2216-5e1e-4f96-baf8-6c7e43c6901b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmStep_contDiff

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
theorem _root_.solution : ContDiff ℝ ∞ rmRho' := by
  unfold rmRho'
  exact (rmStep_contDiff.sub (rmStep_contDiff.comp contDiff_neg)).div_const 2
end ReciprocityTheory.L2DbarEstimates.Y
