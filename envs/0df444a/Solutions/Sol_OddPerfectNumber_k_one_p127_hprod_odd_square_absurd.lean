-- Prove2me | solution 1 for OddPerfectNumber.k_one_p127_hprod_odd_square_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T22:58:41.91537+00:00
-- url     : https://prove2.me/submissions/1b115b12-22e2-45a8-83b7-d4ab862f0bdd

import Mathlib

theorem solution (p m d : Nat)
    (hm : Odd m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hp127 : p = 127) :
    False := by
  subst p
  have h64 : 64 ∣ m ^ 2 := by
    refine ⟨d, ?_⟩
    norm_num at hprod
    simpa [Nat.mul_comm] using hprod
  have h2sq : 2 ∣ m ^ 2 := dvd_trans (by norm_num) h64
  have h2m : 2 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2sq
  rcases hm with ⟨u, hu⟩
  rcases h2m with ⟨v, hv⟩
  omega
