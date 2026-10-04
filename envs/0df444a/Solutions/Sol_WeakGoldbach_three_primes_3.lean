-- Prove2me | solution 3 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T23:30:58.214765+00:00
-- url     : https://prove2.me/submissions/fa790021-a0ae-4ad5-acfd-c35057c46ade
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_goldbach_odd_variant

/-- Every odd natural `n > 1` is a sum of at most three primes.

The analytic content is supplied by the imported platform theorem
`goldbach_odd_variant` (Helfgott's weak Goldbach theorem).  This file performs
the reduction from that three-witness statement to the `Multiset` existential,
and discharges the finitely many small values. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  rcases hodd with ⟨k, hk⟩
  have hnot2 : ¬ 2 ∣ n := by
    intro h2
    rcases h2 with ⟨t, ht⟩
    omega
  by_cases hsmall : n ≤ 7
  · have hcases : n = 3 ∨ n = 5 ∨ n = 7 := by
      interval_cases n <;> omega
    rcases hcases with rfl | rfl | rfl
    · refine ⟨3 ::ₘ 0, by simp, ?_, by simp⟩
      intro x hx
      have hx3 : x = 3 := by simpa using hx
      simpa [hx3] using (show Nat.Prime 3 by norm_num)
    · refine ⟨5 ::ₘ 0, by simp, ?_, by simp⟩
      intro x hx
      have hx5 : x = 5 := by simpa using hx
      simpa [hx5] using (show Nat.Prime 5 by norm_num)
    · refine ⟨7 ::ₘ 0, by simp, ?_, by simp⟩
      intro x hx
      have hx7 : x = 7 := by simpa using hx
      simpa [hx7] using (show Nat.Prime 7 by norm_num)
  · have hbig : 7 < n := by omega
    obtain ⟨p, q, r, hp, hq, hr, hsum⟩ := goldbach_odd_variant n hbig hnot2
    refine ⟨p ::ₘ q ::ₘ r ::ₘ 0, by simp, ?_, ?_⟩
    · intro x hx
      simp at hx
      rcases hx with hxp | hxq | hxr
      · simpa [hxp] using hp
      · simpa [hxq] using hq
      · simpa [hxr] using hr
    · simp only [Multiset.sum_cons, Multiset.sum_zero]
      omega
