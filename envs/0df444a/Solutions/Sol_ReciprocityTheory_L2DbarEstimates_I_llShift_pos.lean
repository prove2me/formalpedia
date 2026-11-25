-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.llShift_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:38.952399+00:00
-- url     : https://prove2.me/submissions/d1928198-fca7-4df2-9d10-385ce57ab0fc

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 < llShift c t := by
  unfold llShift
  set s := Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) with hs
  have h0 : 0 ≤ s := Real.smoothTransition.nonneg _
  have h1 : s ≤ 1 := Real.smoothTransition.le_one _
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; norm_num
  · have ht : 0 < (t + 3 * c / 4) / (c / 4) := by
      by_contra hn
      have := Real.smoothTransition.zero_of_nonpos (not_lt.mp hn)
      rw [← hs] at this; linarith
    have ht' : 0 < t + 3 * c / 4 := by
      have := (div_pos_iff.mp ht)
      rcases this with h2 | h2
      · exact h2.1
      · linarith [h2.2]
    nlinarith
end ReciprocityTheory.L2DbarEstimates.I
