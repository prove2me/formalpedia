-- Prove2me | solution 1 for OddPerfectNumber.order_three_mod_587_eq_293
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T16:34:25.015584+00:00
-- url     : https://prove2.me/submissions/77a59fba-de39-4ee4-b912-a5da227dbcf5

import Mathlib

theorem solution : orderOf (3 : ZMod 587) = 293 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (x := (3 : ZMod 587)) (n := 293) (by norm_num)
  · set_option maxRecDepth 100000 in decide
  · intro r hr hdiv
    have hre : r = 293 :=
      (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 293)).mp hdiv
    subst r
    decide
