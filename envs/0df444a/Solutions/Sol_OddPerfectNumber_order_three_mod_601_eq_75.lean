-- Prove2me | solution 1 for OddPerfectNumber.order_three_mod_601_eq_75
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T16:01:00.315433+00:00
-- url     : https://prove2.me/submissions/c182e058-4a81-4231-9ecb-d0eea057498f

import Mathlib

theorem solution : orderOf (3 : ZMod 601) = 75 := by
  apply (orderOf_eq_iff (x := (3 : ZMod 601)) (by norm_num)).2
  constructor
  · decide
  · intro n hn hnpos
    interval_cases n <;> decide
