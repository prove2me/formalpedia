-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rmStep_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:48.404044+00:00
-- url     : https://prove2.me/submissions/a9c3efa5-9b29-4525-978b-f1f587f0ec53

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
theorem _root_.solution : ContDiff ℝ ∞ rmStep := by
  unfold rmStep
  exact (contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))).sub
    contDiff_const
end ReciprocityTheory.L2DbarEstimates.Y
