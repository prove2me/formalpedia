-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.dualSig_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:40:26.438674+00:00
-- url     : https://prove2.me/submissions/7068540c-e05d-4192-af90-b49acda53fd0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_AddLogPosOfThreeQuartersLe

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
universe u
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (s : ℝ) : 3 / 4 ≤ dualSig s := by
  unfold dualSig
  rcases le_or_gt s (3 / 4) with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by nlinarith)]
    simp
  · have := Real.smoothTransition.nonneg ((s - 3 / 4) * 8)
    nlinarith
end ReciprocityTheory.L2DbarEstimates.I
