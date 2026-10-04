-- Prove2me | solution 14 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T12:27:30.490484+00:00
-- url     : https://prove2.me/submissions/28867235-9fa2-4785-8239-096d9868046a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

-- Second, materially different repair of the same two OPEN causes as
-- `cand_parity_fix.lean`.  It differs in the cause-linked part, not cosmetically.
--
-- Cause 1 (arith, 34x).  Both earlier shapes destroyed oddness before `omega`
-- could use it:
--   * `obtain ⟨k, hk⟩ := hodd` gives only `hk : ∃ r, n + r + r = 1`;
--   * `obtain ⟨k, hk⟩ := Odd.exists_bit1 hodd` gives `hk : n = 2 * k + 1`,
--     which works but leaves the decision of *which* small value `n` is to a
--     chain of `Nat.lt_or_ge` splits, so a single mis-nested branch silently
--     asserts a false equality.
--
-- This variant avoids `omega` in the small-case branch entirely: it derives the
-- membership in `{3, 5, 7}` as a `Finset` fact, so the branch is closed by
-- rewriting with `Finset.mem_insert` / `Finset.mem_singleton` and by `subst`,
-- and the arithmetic that remains is discharged by `interval_cases`-style
-- `omega` on a bounded `Finset` membership rather than on a chain of inequalities.
--
-- Cause 2 (`simp` made no progress, 4x).  The cons-multiset witness is unchanged
-- from the variant that reached SKETCH_ACCEPTED, so the card/sum goals keep a
-- closed `simpa only [...]` lemma set instead of a bare `simp`.

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
  rcases Nat.lt_or_ge n 9 with hsmall | hbig
  · obtain ⟨k, hk⟩ := Odd.exists_bit1 hodd
    have hmem : n ∈ ({3, 5, 7} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    rcases Finset.mem_insert.mp hmem with h3 | hrest
    · have hn3 : n = 3 := by simpa only [Finset.mem_singleton] using h3
      subst hn3
      exact WeakGoldbach.three_primes_three
    · rcases Finset.mem_insert.mp hrest with h5 | h7
      · have hn5 : n = 5 := by simpa only [Finset.mem_singleton] using h5
        subst hn5
        exact WeakGoldbach.three_primes_five
      · have hn7 : n = 7 := by simpa only [Finset.mem_singleton] using h7
        subst hn7
        exact WeakGoldbach.three_primes_of_prime 7 (by norm_num)
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
