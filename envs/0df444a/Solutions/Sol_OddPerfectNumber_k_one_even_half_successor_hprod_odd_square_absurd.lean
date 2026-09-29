-- Prove2me | solution 1 for OddPerfectNumber.k_one_even_half_successor_hprod_odd_square_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T23:06:35.780401+00:00
-- url     : https://prove2.me/submissions/05ebd99c-d818-42c0-8414-f55a71debeec

import Mathlib

theorem solution (p m d : Nat)
    (hm : Odd m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hDeven : Even ((p + 1) / 2)) :
    False := by
  have h2D : 2 ∣ (p + 1) / 2 := by
    rcases hDeven with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    omega
  have h2sq : 2 ∣ m ^ 2 := by
    rw [hprod]
    exact dvd_mul_of_dvd_left h2D d
  have h2m : 2 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2sq
  rcases hm with ⟨u, hu⟩
  rcases h2m with ⟨v, hv⟩
  omega
