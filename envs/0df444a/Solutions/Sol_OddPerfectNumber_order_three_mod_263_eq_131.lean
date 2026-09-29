-- Prove2me | solution 1 for OddPerfectNumber.order_three_mod_263_eq_131
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T16:36:50.027996+00:00
-- url     : https://prove2.me/submissions/d169db91-6541-42fa-91f0-69bc828d13c1

import Mathlib

theorem solution : orderOf (3 : ZMod 263) = 131 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (x := (3 : ZMod 263)) (n := 131) (by norm_num)
  · set_option maxRecDepth 100000 in decide
  · intro r hr hdiv
    have hre : r = 131 :=
      (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 131)).mp hdiv
    subst r
    decide
