-- Prove2me | solution 1 for actuarial_f_annual_floor_at_least_first
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:46.773004+00:00
-- url     : https://prove2.me/submissions/bcf61494-8f3f-4d40-9b09-c88a82329adb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_annualFloorPayment

open ActuarialUnderpinsF

theorem solution (a b ga gb : ℕ → ℝ)
    (z t : ℕ) : a z * ga t ≤ annualFloorPayment a b ga gb z t := by
  exact le_max_left _ _
