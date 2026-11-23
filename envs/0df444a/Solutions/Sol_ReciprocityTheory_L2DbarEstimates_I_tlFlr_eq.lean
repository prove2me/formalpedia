-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tlFlr_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:20.617895+00:00
-- url     : https://prove2.me/submissions/1a091160-622a-4240-a721-ba228935461c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA

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
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (a b s : ℝ) (hab : b < a) (h : a ≤ s) : tlFlr a b s = s := by
  unfold tlFlr
  have h1 : (a - s) / (a - b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [Real.smoothTransition.zero_of_nonpos h1]; ring
end ReciprocityTheory.L2DbarEstimates.I
