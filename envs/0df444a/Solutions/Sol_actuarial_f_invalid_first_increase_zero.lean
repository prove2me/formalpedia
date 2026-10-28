-- Prove2me | solution 1 for actuarial_f_invalid_first_increase_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:17.489985+00:00
-- url     : https://prove2.me/submissions/3a155ac8-c98a-4e87-a14a-f1287cf3debe

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyScheduledRate

open ActuarialUnderpinsF

theorem solution
    (r first t : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (hf : first ≤ r) :
    monthlyScheduledRate r first floor cap inflation t = 0 := by
  unfold monthlyScheduledRate
  rw [if_neg (by omega), if_neg (by omega)]
