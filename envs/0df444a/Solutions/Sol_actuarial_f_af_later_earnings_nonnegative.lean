-- Prove2me | solution 1 for actuarial_f_af_later_earnings_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:57:47.790492+00:00
-- url     : https://prove2.me/submissions/63411440-0040-4413-bc69-e70ced4c6d52

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afLaterEarningsAddition

open ActuarialUnderpinsF



theorem solution
    (relevant gmp assumed : ℝ) :
    0 ≤ afLaterEarningsAddition relevant gmp assumed := by
  exact le_max_left _ _
