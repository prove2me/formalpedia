-- Prove2me | solution 1 for actuarial_f_lpi_zero_floor_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:10.650203+00:00
-- url     : https://prove2.me/submissions/b50c9e8a-5e53-4960-a9e9-347de84d3d2b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem solution (cap observed : ℝ)
    (hc : 0 ≤ cap) : 0 ≤ lpiRate 0 cap observed := by
  unfold lpiRate
  exact le_min hc (le_max_left _ _)
