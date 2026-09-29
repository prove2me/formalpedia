-- Prove2me | solution 1 for OddPerfectNumber.order_37_mod_73_eq_9_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T06:54:14.722141+00:00
-- url     : https://prove2.me/submissions/c8520162-669e-42e9-8019-45bd7118670c

import Mathlib

theorem solution : orderOf (37 : ZMod 73) = 9 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (x := (37 : ZMod 73)) (n := 9) (by norm_num)
  · set_option maxRecDepth 100000 in decide
  · intro r hr hdiv
    have hdivpow : r ∣ 3 ^ 2 := by
      norm_num at hdiv
      norm_num
      exact hdiv
    have hdiv3 : r ∣ 3 := hr.dvd_of_dvd_pow hdivpow
    have hre : r = 3 :=
      (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 3)).mp hdiv3
    subst r
    decide
