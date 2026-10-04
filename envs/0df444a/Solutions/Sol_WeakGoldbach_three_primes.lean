-- Prove2me | solution 1 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-10T12:13:08.695338+00:00
-- url     : https://prove2.me/submissions/9e83b15a-38c3-4f25-bb82-47a8f5f11610
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_goldbach_odd_variant

theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  by_cases hlarge : 7 < n
  · obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
      goldbach_odd_variant n hlarge hodd.not_two_dvd_nat
    refine ⟨{p, q, r}, by simp, ?_, ?_⟩
    · simpa [hp, hq, hr]
    · simpa [add_assoc] using hsum.symm
  · have hle : n ≤ 7 := by omega
    rcases hodd with ⟨k, hk⟩
    have hcases : n = 3 ∨ n = 5 ∨ n = 7 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact ⟨{3}, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨{5}, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨{7}, by norm_num, by norm_num, by norm_num⟩
