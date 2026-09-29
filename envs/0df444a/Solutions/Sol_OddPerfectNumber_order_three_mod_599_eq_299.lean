-- Prove2me | solution 1 for OddPerfectNumber.order_three_mod_599_eq_299
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T16:34:32.423765+00:00
-- url     : https://prove2.me/submissions/5f72b470-0105-4276-aacb-b8dc2058c153

import Mathlib

theorem solution : orderOf (3 : ZMod 599) = 299 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (x := (3 : ZMod 599)) (n := 299) (by norm_num)
  · set_option maxRecDepth 100000 in decide
  · intro r hr hdiv
    have hfactor : (299 : Nat) = 13 * 23 := by norm_num
    rw [hfactor] at hdiv
    rcases (Nat.Prime.dvd_mul hr).mp hdiv with h13 | h23
    · have hre : r = 13 :=
        (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 13)).mp h13
      subst r
      set_option maxRecDepth 100000 in decide
    · have hre : r = 23 :=
        (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 23)).mp h23
      subst r
      set_option maxRecDepth 100000 in decide
