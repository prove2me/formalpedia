-- Prove2me | solution 1 for OddPerfectNumber.order_three_mod_five_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T07:57:46.396975+00:00
-- url     : https://prove2.me/submissions/58dceadf-f897-47da-a7e4-8fe9f4d583bc

import Mathlib

theorem solution : orderOf (3 : ZMod 5) = 4 := by
  apply (orderOf_eq_iff (x := (3 : ZMod 5)) (by norm_num)).2
  constructor
  · decide
  · intro n hn hnpos
    interval_cases n <;> decide
