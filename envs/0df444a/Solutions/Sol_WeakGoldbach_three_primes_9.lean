-- Prove2me | solution 9 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T00:32:57.587986+00:00
-- url     : https://prove2.me/submissions/3a67262a-20c7-4a0d-aa36-289a59c524f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_ternary_goldbach_helfgott_above_10pow27

theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  -- Repack a three-prime equation into the target's multiset form. The sum is
  -- stated *right*-associated as `p + (q + r) = n`, which is exactly the shape
  -- `Multiset.sum_cons` produces for `p ::ₘ q ::ₘ r ::ₘ 0`, so it closes by
  -- `simpa` with no reassociation needed.
  have key : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → p + (q + r) = n →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro p q r hp hq hr hsum
    -- `{p, q, r}` notation is `insert p (insert q (insert r 0))`, so it is
    -- a cons chain only after `cons_zero`; write it explicitly to keep the
    -- membership and sum rewrites in cons form.
    refine ⟨p ::ₘ q ::ₘ r ::ₘ (0 : Multiset ℕ), by simp, ?_, ?_⟩
    · intro t ht
      rcases Multiset.mem_cons.mp ht with ht | ht
      · exact ht ▸ hp
      · rcases Multiset.mem_cons.mp ht with ht | ht
        · exact ht ▸ hq
        · rcases Multiset.mem_cons.mp ht with ht | ht
          · exact ht ▸ hr
          · exact absurd ht (by simp)
    · -- `sum` over `p :: q :: r :: 0` reduces by `sum_cons` to
      -- `p + (q + (r + sum 0))`, and `sum 0 = 0`, which is exactly the
      -- right-associated `p + (q + r) = n` that `key` is stated with.
      simpa only [Multiset.sum_cons, Multiset.sum_zero, add_zero] using hsum
  rcases Nat.lt_or_ge n 9 with hsmall | hbig
  · -- Below the computational floor: the only odd `n` with `1 < n < 9` are 3,
    -- 5 and 7, and 7 is prime, so `three_primes_of_prime` covers it directly.
    -- `Odd n` is `∃ k, n = 2 * k + 1`; exposing it lets `omega` drop the even
    -- candidates without needing any parity lemma.
    obtain ⟨k, hk⟩ := hodd
    have hcases : n = 3 ∨ n = 5 ∨ n = 7 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact WeakGoldbach.three_primes_three
    · exact WeakGoldbach.three_primes_five
    · exact WeakGoldbach.three_primes_of_prime 7 (by norm_num)
  -- Case split on the verified computational bound `B = 8875...e30`.
  have hb : n ≤ 8875694145621773516800000000000 ∨
      8875694145621773516800000000000 < n := by omega
  rcases hb with hb | hb
  · obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
      WeakGoldbach.verified_three_odd_primes_to_8875e30 n (by omega) hb hodd
    exact key p q r hp hq hr (by omega)
  · obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
      WeakGoldbach.ternary_goldbach_helfgott_above_10pow27 n hodd (by omega)
    exact key p q r hp hq hr (by omega)
