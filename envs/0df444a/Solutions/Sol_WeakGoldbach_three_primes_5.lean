-- Prove2me | solution 5 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T09:36:32.222963+00:00
-- url     : https://prove2.me/submissions/61cd3a05-0d63-41f4-8eca-05952f1de9d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_10pow27_to_exp3100
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_exp3100

theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have key : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → p + q + r = n →
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
    · simpa [Multiset.sum_cons, Multiset.sum_zero, add_assoc] using hsum
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
        · have h9 : 9 ≤ n := by
            rcases hodd with ⟨k, hk⟩
            omega
          by_cases hT : n ≤ 8875694145621773516800000000000
          · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
              WeakGoldbach.verified_three_odd_primes_to_8875e30 n h9 hT hodd
            exact key p q r hp hq hr hsum.symm
          · by_cases hexp : Real.exp 3100 ≤ (n : ℝ)
            · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
                WeakGoldbach.three_odd_primes_ge_exp3100 n hexp hodd
              exact key p q r hp hq hr hsum.symm
            · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
                WeakGoldbach.three_odd_primes_10pow27_to_exp3100 n (by omega)
                (lt_of_not_ge hexp) hodd
              exact key p q r hp hq hr hsum.symm
