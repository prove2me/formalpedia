-- Prove2me | solution 11 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T10:20:52.920442+00:00
-- url     : https://prove2.me/submissions/f588c7dd-947b-4f63-b0c8-bfc2b09c9bbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_ternary_goldbach_helfgott_above_10pow27

set_option maxRecDepth 10000 in
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  -- Variant U. Causal repair of 5560 (cand_r).
  --
  --  1. cand_r closed the `sum` goal with `hsum.symm` but without `add_assoc`,
  --     so `simpa only [...]` produced `p + q + r = n` against a goal of
  --     `p + (q + r) = n`. Adding `add_assoc` to the simp set fixes it.
  --  2. The `n < 9` case needed `omega` to see parity, but `Odd n` is a
  --     STRUCTURE and `omega` does not unfold structures. Here the parity is
  --     made explicit by rewriting the oddness equation `n = 2 * k + 1` before
  --     asking `omega` anything, using `Nat.le_of_lt_succ` / `omega` on the
  --     concrete bound rather than a three-way disjunction.
  --
  -- The upper band goes to the single Helfgott child, so there is no
  -- `exp 3100` arithmetic anywhere in the file.
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
  have hodd' : Odd n := hodd
  obtain ⟨k, hk⟩ := hodd'
  rcases Nat.lt_or_ge n 9 with hsmall | hbig
  · -- `hk : n = 2 * k + 1` and `hsmall : n < 9` give `k ≤ 3`, so `k ∈ {0,1,2,3}`
    -- and `n = 2*k+1 ∈ {1,3,5,7}`.  `hn : 1 < n` removes `n = 1`.
    have hcases : n = 3 ∨ n = 5 ∨ n = 7 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact WeakGoldbach.three_primes_three
    · exact WeakGoldbach.three_primes_five
    · exact WeakGoldbach.three_primes_of_prime 7 (by norm_num)
  rcases Nat.lt_or_ge n (10 ^ 27) with hlt27 | hge27
  · have hlo : 7 ≤ n := by omega
    have hhi : n ≤ 8875694145621773516800000000000 := by
      have : (10 ^ 27 : ℕ) ≤ 8875694145621773516800000000000 := by norm_num
      omega
    obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
      WeakGoldbach.verified_three_primes_to_8875e30 n hlo hhi hodd
    exact key p q r hp hq hr (by omega)
  obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
    WeakGoldbach.ternary_goldbach_helfgott_above_10pow27 n hodd hge27
  exact key p q r hp hq hr (by omega)
