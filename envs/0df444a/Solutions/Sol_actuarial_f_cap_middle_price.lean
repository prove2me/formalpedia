-- Prove2me | solution 1 for actuarial_f_cap_middle_price
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:43.07238+00:00
-- url     : https://prove2.me/submissions/4861df63-5f66-4988-8b91-f17361e806c7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem solution :
    lpiRate 0 (5/100 : ℝ) (3/100) = (3/100 : ℝ) := by
  unfold lpiRate
  rw [max_eq_right (by grind : (0:ℝ) ≤ 3/100), min_eq_right (by grind : (3/100:ℝ) ≤ 5/100)]
