-- Prove2me | solution 1 for actuarial_f_lpi_inside
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:19.718452+00:00
-- url     : https://prove2.me/submissions/01781773-5199-4a2a-9e12-967905c115ab

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate

open ActuarialUnderpinsF

theorem solution (floor cap x : ℝ)
    (hlo : floor ≤ x) (hhi : x ≤ cap) :
    lpiRate floor cap x = x := by
  unfold lpiRate
  rw [max_eq_right hlo, min_eq_right hhi]
