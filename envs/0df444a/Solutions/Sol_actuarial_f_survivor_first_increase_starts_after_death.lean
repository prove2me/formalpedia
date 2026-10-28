-- Prove2me | solution 1 for actuarial_f_survivor_first_increase_starts_after_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:02:50.452388+00:00
-- url     : https://prove2.me/submissions/8297cb0a-6b4b-4b84-adf3-bca4bd64a4b9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyScheduledGrowth

open ActuarialUnderpinsF



theorem solution
    (i first : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (hfirst : i + 1 < first) :
    monthlyScheduledGrowth (i + 1) first floor cap inflation (i + 1) = 1 := by
  unfold monthlyScheduledGrowth
  apply Finset.prod_eq_one
  intro m hm
  rw [Finset.mem_range] at hm
  unfold monthlyScheduledRate
  rw [if_neg (by omega), if_neg (by omega)]
  norm_num
