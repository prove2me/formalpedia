-- Prove2me | solution 1 for WeakGoldbach.verified_three_primes_to_8875e30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T02:58:55.495634+00:00
-- url     : https://prove2.me/submissions/7bae41e3-635e-4b09-9c3b-062ac1b53f1a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_verified_two_primes_to_4e18
import Theorems.Thm_WeakGoldbach_prime_in_window_4e18_add_two
import Theorems.Thm_WeakGoldbach_two_primes_4e18_add_two

theorem solution (n : ℕ) (hlo : 7 ≤ n)
    (hhi : n ≤ 8875694145621773516800000000000) (hodd : Odd n) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r := by
  obtain ⟨k, hk⟩ := hodd
  have hodd : Odd n := ⟨k, hk⟩
  by_cases hsmall : n ≤ 4 * 10 ^ 18 + 3
  · obtain ⟨a, b, ha, hb, hab⟩ :=
      WeakGoldbach.verified_two_primes_to_4e18 (n - 3) (by omega) (by omega)
        ⟨k - 1, by omega⟩
    exact ⟨3, a, b, by norm_num, ha, hb, by omega⟩
  · obtain ⟨p, hp, h4, hB⟩ :=
      WeakGoldbach.prime_in_window_4e18_add_two n hodd (by omega) hhi
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two (by omega)
    by_cases hedge : n - p = 4 * 10 ^ 18 + 2
    · obtain ⟨a, b, ha, hb, hab⟩ := WeakGoldbach.two_primes_4e18_add_two
      exact ⟨p, a, b, hp, ha, hb, by omega⟩
    · obtain ⟨a, b, ha, hb, hab⟩ :=
        WeakGoldbach.verified_two_primes_to_4e18 (n - p) h4 (by omega)
          ⟨k - j, by omega⟩
      exact ⟨p, a, b, hp, ha, hb, by omega⟩
