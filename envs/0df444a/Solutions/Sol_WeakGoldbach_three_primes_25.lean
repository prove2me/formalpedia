-- Prove2me | solution 25 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T20:37:52.989169+00:00
-- url     : https://prove2.me/submissions/58dbdf07-cdb0-480e-82bc-47e46d532933
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_9
import Theorems.Thm_WeakGoldbach_three_primes_of_prime

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

Two-case reduction onto the Open child
`WeakGoldbach.ternary_goldbach_all_odd_9` (`e987963c`).

Repairs candidates 6446, 6450 and 6456, whose compiler evidence identified
three independent faults, all in the `n < 9` branch:

* 6446 E02: the sibling name `ternary_goldbach_all_odd_ge_9` was unknown because
  that candidate imported this module. This file imports the module matching
  the name it calls, and reduces through `ternary_goldbach_all_odd_9`.
* 6450 E01 / 6456 E02: `simp` made no progress at the membership test, because
  the literal `{p, q, r}` is `insert r (cons q (cons p nil))` rather than a
  syntactic cons chain. `Multiset.insert_eq_cons` exposes it.
* 6456 E01: `interval_cases k <;> norm_num` left the `k = 0` branch open. The
  reported goal state shows Lean had already substituted `hk`, leaving
  `hk : n = 2 * 0 + 1` with the residual goal `False`, which `hn : 1 < n` refutes;
  `norm_num` on `Nat.Prime n` does not use `hn`, so it cannot close it. This
  branch is therefore decided by `omega` from `hn` alone, never by trying to
  prove `Nat.Prime 1`. The surviving values are exactly `n = 3, 5, 7`, each
  prime, discharged by the Proved `three_primes_of_prime`.

The `n < 9` split is taken on `n` directly rather than on `k`, which keeps the
small-value argument as plain linear arithmetic and matches the shape accepted
for this target in candidate 6004. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  rcases lt_or_ge n 9 with hlt | hge
  · obtain ⟨k, hk⟩ := hodd
    have hn' : n = 2 * k + 1 := hk
    have hprime : Nat.Prime n := by
      rcases Nat.lt_or_ge n 5 with h5 | h5
      · have : n = 3 := by omega
        norm_num [this]
      · rcases Nat.lt_or_ge n 7 with h7 | h7
        · have : n = 5 := by omega
          norm_num [this]
        · have : n = 7 := by omega
          norm_num [this]
    exact WeakGoldbach.three_primes_of_prime n hprime
  · obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
      WeakGoldbach.ternary_goldbach_all_odd_9 n hge hodd
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
