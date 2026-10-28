-- Prove2me | solution 1 for actuarial_f_before_first_increase_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:21.117109+00:00
-- url     : https://prove2.me/submissions/2e4f198d-3d35-4eda-abb1-a992cedc6d7e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyScheduledRate

open ActuarialUnderpinsF

theorem solution
    (r first t : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (ht : t < first) :
    monthlyScheduledRate r first floor cap inflation t = 0 := by
  unfold monthlyScheduledRate
  rw [if_neg (by omega), if_neg (by omega)]
