-- Prove2me | solution 2 for WeakGoldbach.verified_three_primes_to_8875e30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T11:11:30.645992+00:00
-- url     : https://prove2.me/submissions/f595c944-65ef-4bb0-b19d-7226e909f025
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_verified_two_primes_to_4e18
import Theorems.Thm_WeakGoldbach_prime_in_window_4e18_add_two
import Theorems.Thm_WeakGoldbach_two_primes_4e18_add_two

namespace WeakGoldbach

theorem _root_.solution (n : ℕ) (hlo : 7 ≤ n)
    (hhi : n ≤ 8875694145621773516800000000000) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.1 hodd
  by_cases hsmall : n ≤ 4 * 10 ^ 18 + 3
  · have he : Even (n - 3) := by rw [Nat.even_iff]; omega
    obtain ⟨p, q, hp, hq, hpq⟩ :=
      WeakGoldbach.verified_two_primes_to_4e18 (n - 3) (by omega) (by omega) he
    exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩
  · push_neg at hsmall
    obtain ⟨p, hp, hlo2, hhi2⟩ :=
      WeakGoldbach.prime_in_window_4e18_add_two n hodd (by omega) hhi
    have hpne : p ≠ 2 := by omega
    have hpar : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left hpne
    have he : Even (n - p) := by rw [Nat.even_iff]; omega
    by_cases hcase : n - p ≤ 4 * 10 ^ 18
    · obtain ⟨a, b, ha, hb, hab⟩ :=
        WeakGoldbach.verified_two_primes_to_4e18 (n - p) hlo2 hcase he
      exact ⟨p, a, b, hp, ha, hb, by omega⟩
    · obtain ⟨a, b, ha, hb, hab⟩ := WeakGoldbach.two_primes_4e18_add_two
      exact ⟨p, a, b, hp, ha, hb, by omega⟩

end WeakGoldbach

#print axioms solution
