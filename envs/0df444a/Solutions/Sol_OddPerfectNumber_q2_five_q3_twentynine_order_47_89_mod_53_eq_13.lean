-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_order_47_89_mod_53_eq_13
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T14:45:10.348262+00:00
-- url     : https://prove2.me/submissions/c19ad6f0-5057-4685-bd4c-c96c90eae448

import Mathlib

theorem solution : orderOf (47 : ZMod 53) = 13 ∧ orderOf (89 : ZMod 53) = 13 := by
  constructor
  · apply orderOf_eq_of_pow_and_pow_div_prime (x := (47 : ZMod 53)) (n := 13) (by norm_num)
    · decide
    · intro r hr hdiv
      have hdiv13 : r ∣ 13 := by
        norm_num at hdiv
        exact hdiv
      have hre : r = 13 :=
        (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 13)).mp hdiv13
      subst r
      decide
  · apply orderOf_eq_of_pow_and_pow_div_prime (x := (89 : ZMod 53)) (n := 13) (by norm_num)
    · decide
    · intro r hr hdiv
      have hdiv13 : r ∣ 13 := by
        norm_num at hdiv
        exact hdiv
      have hre : r = 13 :=
        (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 13)).mp hdiv13
      subst r
      decide
