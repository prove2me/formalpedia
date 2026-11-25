-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.basic_exp_seven
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:38.700577+00:00
-- url     : https://prove2.me/submissions/790eae5b-a12f-4313-b3b0-8c90f3743014

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BasicExpBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution : Real.exp 7 ≤ 1250 := by
  have h := Real.exp_one_lt_d9
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 7 ≤ (2.7182818286 : ℝ) ^ 7 := by gcongr
    _ ≤ 1250 := by norm_num
end ReciprocityTheory.L2DbarEstimates.I
