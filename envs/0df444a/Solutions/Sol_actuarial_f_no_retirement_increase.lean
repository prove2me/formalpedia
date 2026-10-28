-- Prove2me | solution 1 for actuarial_f_no_retirement_increase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:28.701065+00:00
-- url     : https://prove2.me/submissions/88da57a1-ba87-4418-94bf-7cf3e815d025

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyScheduledGrowth

open ActuarialUnderpinsF

theorem solution
    (r first : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (hr : r < first) :
    monthlyScheduledGrowth r first floor cap inflation r = 1 := by
  unfold monthlyScheduledGrowth
  refine Finset.prod_eq_one fun m hm => ?_
  rw [Finset.mem_range] at hm
  unfold monthlyScheduledRate
  rw [if_neg (by omega), if_neg (by omega)]
  grind
