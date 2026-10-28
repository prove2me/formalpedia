-- Prove2me | solution 1 for actuarial_f_lpi_at_floor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:24.107998+00:00
-- url     : https://prove2.me/submissions/5f62f375-29cf-46fc-9a69-32b1cafdf397

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem solution (floor cap x : ℝ)
    (hfc : floor ≤ cap) (hx : x ≤ floor) :
    lpiRate floor cap x = floor := by
  unfold lpiRate
  rw [max_eq_left hx, min_eq_right hfc]
