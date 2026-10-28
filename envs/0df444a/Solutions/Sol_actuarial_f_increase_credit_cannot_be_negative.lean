-- Prove2me | solution 1 for actuarial_f_increase_credit_cannot_be_negative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:58:11.707199+00:00
-- url     : https://prove2.me/submissions/4297d48a-5c9b-4799-bf4e-0180a08fdd08

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_pensionIncreaseOutstanding

open ActuarialUnderpinsF



theorem solution
    (required credited : ℝ) :
    0 ≤ pensionIncreaseOutstanding required credited := by
  exact le_max_left _ _
