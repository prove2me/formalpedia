-- Prove2me | solution 1 for actuarial_f_post88_gmp_full_three_percent_example
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:59:04.927749+00:00
-- url     : https://prove2.me/submissions/f433433a-7fbf-4761-8e83-685ae5f8a15f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

open ActuarialUnderpinsF



theorem solution :
    gmpPost88AprilIncrease 20261001 20270406
      (fun _ => (7 / 100 : ℝ)) 2027 = (3 / 100 : ℝ) := by
  norm_num [gmpPost88AprilIncrease, gmpStatutoryAprilEligible, gmpSixApril,
    gmpStatutoryPost88OrderRate, lpiRate]
