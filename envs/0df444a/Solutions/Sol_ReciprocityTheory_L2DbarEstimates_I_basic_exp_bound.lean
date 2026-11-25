-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.basic_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:30:09.213792+00:00
-- url     : https://prove2.me/submissions/15f68417-e135-4230-a639-8d256a22bab9

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
theorem _root_.solution (x : ℝ) (hx : 1 ≤ x) :
    (x + 1) ^ 2 + (x + Real.log x) ≤ 2 * Real.exp x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have h4 := Real.sum_le_exp_of_nonneg hx0 4
  simp [Finset.sum_range_succ, Nat.factorial] at h4
  have hl := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x)
  nlinarith [sq_nonneg (x - 7 / 5), mul_nonneg hx0 (sq_nonneg (x - 7 / 5)),
    mul_nonneg (by linarith : (0:ℝ) ≤ x - 1) (sq_nonneg (x - 7 / 5))]
end ReciprocityTheory.L2DbarEstimates.I
