-- Prove2me | solution 1 for actuarial_f_month_proportion_capped
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:52:15.777346+00:00
-- url     : https://prove2.me/submissions/a0ec5485-c117-4f59-8ebe-eb636c6ce86e

import Mathlib
import Definitions.Def_actuarial_f_proratedAnnualRate
open ActuarialUnderpinsF

theorem solution
    (rate : ℝ) (months : ℕ) (h : 12 ≤ months) :
    proratedAnnualRate rate months = rate := by
  unfold proratedAnnualRate
  rw [min_eq_left h]; push_cast; ring
