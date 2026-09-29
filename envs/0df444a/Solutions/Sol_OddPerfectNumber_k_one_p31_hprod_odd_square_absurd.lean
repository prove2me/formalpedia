-- Prove2me | solution 1 for OddPerfectNumber.k_one_p31_hprod_odd_square_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T22:40:37.160211+00:00
-- url     : https://prove2.me/submissions/17324ac3-233c-4d99-86f0-fb5d37ae3c1a

import Mathlib

theorem solution (p m d : Nat)
    (hm : Odd m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hp31 : p = 31) :
    False := by
  subst p
  have h16 : 16 ∣ m ^ 2 := by
    refine ⟨d, ?_⟩
    norm_num at hprod
    simpa [Nat.mul_comm] using hprod
  have h2sq : 2 ∣ m ^ 2 := dvd_trans (by norm_num) h16
  have h2m : 2 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2sq
  rcases hm with ⟨u, hu⟩
  rcases h2m with ⟨v, hv⟩
  omega
