-- Prove2me | solution 9 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T23:29:16.579982+00:00
-- url     : https://prove2.me/submissions/dc838453-15b6-4fc2-953e-f6471d85b3e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_strong_goldbach_conjecture

theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  -- `key` repacks a two-prime equation into the target's multiset form. It is
  -- stated with the sum already oriented as `p + q + 3 = n` so the multiset sum
  -- closes by `simpa` alone, with no arithmetic obligation left to discharge.
  have key : ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → (p + q + 3 = n) →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro p q hp hq hsum
    refine ⟨{p, q, 3}, by simp, ?_, ?_⟩
    · intro t ht
      simp only [Multiset.insert_eq_cons, Multiset.cons_zero, Multiset.mem_cons,
        Multiset.notMem_zero, Multiset.mem_singleton, or_false] at ht
      rcases ht with ht | ht | ht
      · simpa [ht] using hp
      · simpa [ht] using hq
      · simpa [ht] using Nat.prime_three
    · simpa [Multiset.sum_cons, Multiset.sum_zero, add_assoc] using hsum
  by_cases hprime : Nat.Prime n
  · exact WeakGoldbach.three_primes_of_prime n hprime
  · by_cases h3 : n = 3
    · subst n
      exact WeakGoldbach.three_primes_three
    · by_cases h5 : n = 5
      · subst n
        exact WeakGoldbach.three_primes_five
      · -- `Odd n` is opaque to `omega`, so expose it as the linear equation
        -- `n = 2 * k + 1`. Combined with `1 < n`, `n != 3` and `n != 5` this gives
        -- `n >= 7`, hence `n - 3 >= 4`, and `n - 3 = 2 * (k - 1)` is even --
        -- exactly the two hypotheses `strong_goldbach_conjecture` requires.
        obtain ⟨k, hk⟩ := hodd
        have hk1 : 1 ≤ k := by omega
        have h3le : 3 ≤ n := by omega
        have hsub : 4 ≤ n - 3 := by omega
        have heven : 2 ∣ n - 3 := by omega
        obtain ⟨p, q, hp, hq, hpq⟩ :=
          strong_goldbach_conjecture (n - 3) hsub heven
        have hsum : p + q + 3 = n := calc
          p + q + 3 = (n - 3) + 3 := by rw [hpq]
          _ = n := Nat.sub_add_cancel h3le
        exact key p q hp hq hsum
