-- Prove2me | solution 1 for actuarial_f_five_cap_high_price
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:38.487531+00:00
-- url     : https://prove2.me/submissions/0ebfa1a5-76cb-4bcc-82f3-f988e5d2fa52

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem solution :
    lpiRate 0 (5/100 : ℝ) (8/100) = (5/100 : ℝ) := by
  unfold lpiRate
  rw [max_eq_right (by grind : (0:ℝ) ≤ 8/100), min_eq_left (by grind : (5/100:ℝ) ≤ 8/100)]
