-- Prove2me | solution 1 for actuarial_f_day_prorating_full_period
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:58:37.351545+00:00
-- url     : https://prove2.me/submissions/fa71ae56-1dbe-436f-839c-9fa4b6b16726

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_proratedDayRate

open ActuarialUnderpinsF



theorem solution
    (rate : ℝ) (yearDays : ℕ) (hpos : 0 < yearDays) :
    proratedDayRate rate yearDays yearDays = rate := by
  have hne : (yearDays : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [proratedDayRate, if_neg hpos.ne', min_self]
  field_simp
