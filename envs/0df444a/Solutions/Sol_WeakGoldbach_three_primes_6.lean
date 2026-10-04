-- Prove2me | solution 6 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T10:52:08.276705+00:00
-- url     : https://prove2.me/submissions/bf5bc84a-cff7-462f-b8a0-e5ad6f229085
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have key : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → p + q + r = n →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro p q r hp hq hr hsum
    refine ⟨({p, q, r} : Multiset ℕ), by simp, ?_, ?_⟩
    · intro t ht
      simp only [Multiset.insert_eq_cons, Multiset.cons_zero, Multiset.mem_cons,
        Multiset.notMem_zero, Multiset.mem_singleton, or_false] at ht
      rcases ht with ht | ht | ht
      · simpa [ht] using hp
      · simpa [ht] using hq
      · simpa [ht] using hr
    · calc ({p, q, r} : Multiset ℕ).sum
          = p + ({q, r} : Multiset ℕ).sum := by
              rw [Multiset.insert_eq_cons, Multiset.sum_cons]
        _ = p + (q + r) := by
              rw [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
        _ = n := by omega
  have hnot2 : ¬ 2 ∣ n := hodd.not_two_dvd_nat
  by_cases hprime : Nat.Prime n
  · exact WeakGoldbach.three_primes_of_prime n hprime
  · by_cases h3 : n = 3
    · subst n
      exact WeakGoldbach.three_primes_three
    · by_cases h5 : n = 5
      · subst n
        exact WeakGoldbach.three_primes_five
      · by_cases h7 : n = 7
        · subst n
          have hkey : (2 : ℕ) + (2 : ℕ) + (3 : ℕ) = 7 := by norm_num
          exact key 2 2 3 Nat.prime_two Nat.prime_two Nat.prime_three hkey
        · have h7' : 7 ≤ n := by
            rcases hodd with ⟨k, hk⟩
            omega
          by_cases hT : n ≤ 8875694145621773516800000000000
          · obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
              WeakGoldbach.verified_three_primes_to_8875e30 n h7' hT hodd
            exact key p q r hp hq hr hsum.symm
          · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
              WeakGoldbach.three_odd_primes_ge_10pow27 n (by omega) hodd
            exact key p q r hp hq hr hsum.symm
