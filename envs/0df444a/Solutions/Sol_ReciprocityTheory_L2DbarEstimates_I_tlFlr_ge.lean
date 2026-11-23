-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tlFlr_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:22.263946+00:00
-- url     : https://prove2.me/submissions/a01bde7a-7142-4698-b690-81b6fe352a08

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
theorem _root_.solution (a b s : ℝ) (hab : b < a) : b ≤ tlFlr a b s := by
  unfold tlFlr
  have hT0 := Real.smoothTransition.nonneg ((a - s) / (a - b))
  rcases le_total a s with h | h
  · nlinarith [Real.smoothTransition.le_one ((a - s) / (a - b))]
  · rcases le_total s b with h' | h'
    · have : 1 ≤ (a - s) / (a - b) := by rw [le_div_iff₀ (by linarith)]; linarith
      rw [Real.smoothTransition.one_of_one_le this]; linarith
    · nlinarith
end ReciprocityTheory.L2DbarEstimates.I
