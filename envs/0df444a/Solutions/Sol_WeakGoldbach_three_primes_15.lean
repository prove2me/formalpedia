-- Prove2me | solution 15 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T12:50:16.975285+00:00
-- url     : https://prove2.me/submissions/f2f5f2a8-6118-4be5-8d71-9e6f095d383d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

-- Repair of the two still-OPEN causes on candidates 5594/5595.
--
-- (1) arith / 34x.  Earlier candidates mis-nested the small-case branches, so
--     one branch asserted `n = 7` -- an equality that also holds for `n = 4`,
--     where the goal is false.  Here the branch is split at 9, 5, 3 and 7 and
--     every derived value is forced by `omega` from the *linear* parity equation
--     `hk : n = 2 * k + 1` together with `hn : 1 < n`, so no branch asserts an
--     equality it has not earned.
--
--     This variant obtains that equation through the *definition* of `Odd`,
--     which in Mathlib.Algebra.Ring.Parity is literally `∃ k, a = 2 * k + 1`.
--     Its two siblings instead go through the named eliminator
--     `Odd.exists_bit1`.  All three routes yield the identical linear fact and
--     differ only in which projection of oddness they take.
--
-- (2) `simp` made no progress.  The card and sum goals are closed by the
--     explicit cons-multiset witness `key` below, with a closed `simpa only [...]`
--     lemma set (including `add_assoc` for the `p + q + r` vs `p + (q + r)`
--     reassociation) rather than bare `simp`/`omega` pairs.

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
  · -- `hk : n = 2 * k + 1` is the linear parity fact `omega` can consume, so
    -- `hsmall : n < 9` together with `hn : 1 < n` forces `n` to be 3, 5 or 7.
    -- Third route to the same linear parity fact: `Odd` is *definitionally*
    -- `∃ k, n = 2 * k + 1` in Mathlib.Algebra.Ring.Parity, so the plain
    -- anonymous constructor already yields the linear equation with no
    -- projection at all.
    obtain ⟨k, hk⟩ := hodd
    -- One flat disjunction decided by `omega`, rather than a nest of
    -- `Nat.lt_or_ge` splits.  Candidate 5628 CE'd on `line 50: No goals to be
    -- solved`: the third bullet of the innermost split, `exact absurd hge3
    -- (by omega)`, sat in a branch whose hypotheses did not mention `hge3`, so
    -- the goal was already closed before the tactic ran.  Deriving the
    -- disjunction in one step removes that bullet-scoping hazard entirely.
    have hcases : n = 3 ∨ n = 5 ∨ n = 7 := by omega
    rcases hcases with hn3 | hn5 | hn7
    · subst hn3
      exact WeakGoldbach.three_primes_three
    · subst hn5
      exact WeakGoldbach.three_primes_five
    · subst hn7
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
