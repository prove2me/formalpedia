-- Prove2me | solution 16 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T12:51:24.024525+00:00
-- url     : https://prove2.me/submissions/c8f31af2-fc58-4b65-ad40-204f01ffe6a6
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
-- (1) arith / 34x.  The earlier candidates used `obtain ⟨k, hk⟩ := hodd`, which
--     only exposes the oddness as `hk : ∃ r, n + r + r = 1`; `omega` never saw
--     parity, so `n < 9 ∧ 1 < n` left `n ∈ {2,…,8}` open and the branch
--     claiming `n = 7` was unprovable (true for `n = 4` as well, where the
--     goal is false).  Here oddness enters as the *linear* equation
--     `hk : n = 2 * k + 1` obtained from `Odd.exists_bit1`, which is exactly the
--     shape `omega` consumes.
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
    obtain ⟨k, hk⟩ := Odd.exists_bit1 hodd
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
