-- Prove2me | solution 1 for actuarial_f_payment_increase_on_retirement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:15.169993+00:00
-- url     : https://prove2.me/submissions/b7d1464b-d16d-4438-b7f2-12ae540ea4f6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_paymentIncrease

open ActuarialUnderpinsF

theorem solution (r : ℕ)
    (increase : ℕ → ℝ) : paymentIncrease r r increase = 1 := by
  simp [paymentIncrease, compoundGrowth]
