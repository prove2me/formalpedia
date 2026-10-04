-- Prove2me | solution 7 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T12:07:54.456592+00:00
-- url     : https://prove2.me/submissions/2791bb5c-c2e5-4633-b87d-4f3b0594970c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_goldbach_odd_variant

theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have key : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → n = p + q + r →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro p q r hp hq hr hsum
    refine ⟨{p, q, r}, by simp, ?_, ?_⟩
    · intro t ht
      simp only [Multiset.insert_eq_cons, Multiset.cons_zero, Multiset.mem_cons,
        Multiset.notMem_zero, Multiset.mem_singleton, or_false] at ht
      rcases ht with ht | ht | ht
      · simpa [ht] using hp
      · simpa [ht] using hq
      · simpa [ht] using hr
    · have hval : p + q + r = n := hsum.symm
      simpa [Multiset.sum_cons, Multiset.sum_zero, add_assoc] using hval
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
          refine ⟨({2, 2, 3} : Multiset ℕ), by simp, ?_, by norm_num⟩
          intro t ht
          simp only [Multiset.insert_eq_cons, Multiset.cons_zero, Multiset.mem_cons,
            Multiset.notMem_zero, Multiset.mem_singleton, or_false] at ht
          rcases ht with ht | ht | ht
          · simpa [ht] using Nat.prime_two
          · simpa [ht] using Nat.prime_two
          · simpa [ht] using Nat.prime_three
        · have hgt7 : 7 < n := by omega
          obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
            goldbach_odd_variant n hgt7 hnot2
          exact key p q r hp hq hr hsum
