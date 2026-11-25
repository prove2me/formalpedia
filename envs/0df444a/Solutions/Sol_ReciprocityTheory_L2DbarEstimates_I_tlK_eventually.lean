-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tlK_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:34:37.146635+00:00
-- url     : https://prove2.me/submissions/b11db301-6ed0-4b0c-bfa8-453ab615964d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlFlr_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section
open Filter Topology
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (c t : ℝ) (ht : t < c - 19 / 20) :
    tlK c =ᶠ[𝓝 t] fun t => -Real.log ((c - t) + Real.log (c - t)) := by
  filter_upwards [Iio_mem_nhds ht] with y hy
  have : tlFlr (19 / 20) (9 / 10) (c - y) = c - y := tlFlr_eq _ _ _ (by norm_num) (by simp at hy; linarith)
  simp only [tlK, this]
end ReciprocityTheory.L2DbarEstimates.I
