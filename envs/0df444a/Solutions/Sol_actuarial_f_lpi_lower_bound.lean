-- Prove2me | solution 1 for actuarial_f_lpi_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:10.901466+00:00
-- url     : https://prove2.me/submissions/950a640d-5c6d-40fc-af08-95e879da13a1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem solution (floor cap x : ℝ) (hfc : floor ≤ cap) :
    floor ≤ lpiRate floor cap x := by
  unfold lpiRate
  exact le_min hfc (le_max_left _ _)
