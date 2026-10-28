-- Prove2me | solution 1 for actuarial_f_lpi_at_cap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:28.652812+00:00
-- url     : https://prove2.me/submissions/d9759510-5123-4a38-be35-52c17a461c88

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem solution (floor cap x : ℝ)
    (hfc : floor ≤ cap) (hx : cap ≤ x) :
    lpiRate floor cap x = cap := by
  unfold lpiRate
  exact min_eq_left (le_trans hx (le_max_right _ _))
