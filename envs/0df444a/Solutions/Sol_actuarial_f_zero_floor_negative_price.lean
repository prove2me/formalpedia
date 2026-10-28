-- Prove2me | solution 1 for actuarial_f_zero_floor_negative_price
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:33.635352+00:00
-- url     : https://prove2.me/submissions/2d42da8e-4198-47dc-9b29-f52fff3a94fd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem solution : 
    lpiRate 0 (5/100 : ℝ) (-2/100) = 0 := by
  unfold lpiRate
  rw [max_eq_left (by grind : (-2/100:ℝ) ≤ 0), min_eq_right (by grind : (0:ℝ) ≤ 5/100)]
