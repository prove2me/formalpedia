-- Prove2me | solution 1 for actuarial_f_valid_date_accepts_leap_29
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:54:48.443292+00:00
-- url     : https://prove2.me/submissions/d8233ba7-3633-423b-8415-9d600b33936f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpValidYYYYMMDD

open ActuarialUnderpinsF



theorem solution :
    gmpValidYYYYMMDD 20280229 := by
  norm_num [gmpValidYYYYMMDD, gmpDaysInMonth, gmpLeapYear]
