-- Prove2me | solution 1 for OddPerfectNumber.order_q4_593_mod_113_eq_7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T20:09:43.047357+00:00
-- url     : https://prove2.me/submissions/1a31bb0b-4cf7-45be-8591-58d945756cfe

import Mathlib

theorem solution : orderOf (593 : ZMod 113) = 7 := by
  apply (orderOf_eq_iff (x := (593 : ZMod 113)) (by norm_num)).2
  constructor
  · decide
  · intro n hn hnpos
    interval_cases n <;> decide
