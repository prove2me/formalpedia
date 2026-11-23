-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.llShift_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:13.29418+00:00
-- url     : https://prove2.me/submissions/c060c8aa-cf4d-4ae7-9f15-8da818ff98eb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogLeviA

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 ≤ t) : llShift c t = t + c := by
  unfold llShift
  have : Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [this]; ring
end ReciprocityTheory.L2DbarEstimates.I
