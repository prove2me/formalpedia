-- Prove2me | solution 1 for actuarial_f_valid_date_rejects_february_30
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:55:16.783839+00:00
-- url     : https://prove2.me/submissions/6d96bf8f-b35c-4875-9057-7fa5f89b59ef

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpValidYYYYMMDD

open ActuarialUnderpinsF



theorem solution :
    ¬ gmpValidYYYYMMDD 20270230 := by
  norm_num [gmpValidYYYYMMDD, gmpDaysInMonth, gmpLeapYear]
