-- Prove2me | solution 8 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T18:34:06.141395+00:00
-- url     : https://prove2.me/submissions/4141cd96-205a-4dbd-8ba9-6a9839e45149
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_ternary_goldbach_helfgott_above_10pow27

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
        · have hge7 : 7 ≤ n := by omega
          by_cases hbig : n ≤ 8875694145621773516800000000000
          · obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
              WeakGoldbach.verified_three_primes_to_8875e30 n hge7 hbig hodd
            exact key p q r hp hq hr hsum
          · have hlo : 10 ^ 27 ≤ n := by
              have h1 : (10 : ℕ) ^ 27 = 1000000000000000000000000000 := by norm_num
              have h2 : 1000000000000000000000000000 < 8875694145621773516800000000000 := by norm_num
              omega
            obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
              WeakGoldbach.ternary_goldbach_helfgott_above_10pow27 n hodd hlo
            exact key p q r hp hq hr hsum
