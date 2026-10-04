-- Prove2me | solution 19 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T01:13:44.816878+00:00
-- url     : https://prove2.me/submissions/b60d2414-b3bd-484f-86a0-81c615296212
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

-- Adds a decidable `Nat.Prime (n - 4)` split that no registered child expresses.
-- When `n - 4` is prime the root's Multiset goal is discharged directly by the
-- explicit cons witness `2 ::ₘ 2 ::ₘ (n - 4) ::ₘ 0`, so the `n = 7` instance no
-- longer needs `three_primes_of_prime` and, more importantly, the 2-branch of
-- the ternary decomposition is discharged here rather than deferred.
open WeakGoldbach

theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have key : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → p + (q + r) = n →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro p q r hp hq hr hsum
    refine ⟨p ::ₘ q ::ₘ r ::ₘ (0 : Multiset ℕ), by simp, ?_, ?_⟩
    · intro t ht
      rcases Multiset.mem_cons.mp ht with ht | ht
      · exact ht ▸ hp
      · rcases Multiset.mem_cons.mp ht with ht | ht
        · exact ht ▸ hq
        · rcases Multiset.mem_cons.mp ht with ht | ht
          · exact ht ▸ hr
          · exact absurd ht (by simp)
    · simpa only [Multiset.sum_cons, Multiset.sum_zero, add_zero, add_assoc] using hsum
  have key2 : Nat.Prime (n - 4) →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro h4
    have htwo : 2 ≤ n - 4 := h4.two_le
    have hge4 : 4 ≤ n := by omega
    refine ⟨2 ::ₘ 2 ::ₘ (n - 4) ::ₘ (0 : Multiset ℕ), by simp, ?_, ?_⟩
    · intro t ht
      rcases Multiset.mem_cons.mp ht with ht | ht
      · exact ht ▸ (by norm_num : Nat.Prime (2 : ℕ))
      · rcases Multiset.mem_cons.mp ht with ht | ht
        · exact ht ▸ (by norm_num : Nat.Prime (2 : ℕ))
        · rcases Multiset.mem_cons.mp ht with ht | ht
          · exact ht ▸ h4
          · exact absurd ht (by simp)
    · simp only [Multiset.sum_cons, Multiset.sum_zero, add_zero]
      omega
  by_cases h4 : Nat.Prime (n - 4)
  · exact key2 h4
  rcases Nat.lt_or_ge n 9 with hsmall | hbig
  · obtain ⟨k, hk⟩ := Odd.exists_bit1 hodd
    rcases Nat.lt_or_ge n 5 with hlt5 | hge5
    · have hn3 : n = 3 := by omega
      subst hn3
      exact WeakGoldbach.three_primes_three
    · rcases Nat.lt_or_ge n 7 with hlt7 | hge7
      · have hn5 : n = 5 := by omega
        subst hn5
        exact WeakGoldbach.three_primes_five
      · have hn7 : n = 7 := by omega
        subst hn7
        refine ⟨(2 ::ₘ 2 ::ₘ 3 ::ₘ (0 : Multiset ℕ)), by simp, ?_, ?_⟩
        · intro t ht
          rcases Multiset.mem_cons.mp ht with ht | ht
          · exact ht ▸ (by norm_num : Nat.Prime (2 : ℕ))
          · rcases Multiset.mem_cons.mp ht with ht | ht
            · exact ht ▸ (by norm_num : Nat.Prime (2 : ℕ))
            · rcases Multiset.mem_cons.mp ht with ht | ht
              · exact ht ▸ (by norm_num : Nat.Prime (3 : ℕ))
              · exact absurd ht (by simp)
        · norm_num
  · rcases Nat.lt_or_ge n (10 ^ 27) with hlt27 | hge27
    · have hlo : 7 ≤ n := by omega
      have hhi : n ≤ 8875694145621773516800000000000 := by
        have hh : (10 ^ 27 : ℕ) ≤ 8875694145621773516800000000000 := by norm_num
        omega
      obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
        WeakGoldbach.verified_three_primes_to_8875e30 n hlo hhi hodd
      exact key p q r hp hq hr (by omega)
    · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
        WeakGoldbach.three_odd_primes_ge_10pow27 n hge27 hodd
      exact key p q r hp hq hr (by omega)
