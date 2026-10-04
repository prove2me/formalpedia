-- Prove2me | solution 31 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T23:49:59.727447+00:00
-- url     : https://prove2.me/submissions/3179eddb-9a28-45ef-88a9-983151360d89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_ternary_goldbach_helfgott_above_10pow27
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

Second two-child hybrid, differing from candidate 6534 in the cause-linked
part: the finite child is `verified_three_primes_to_8875e30` rather than
`verified_three_odd_primes_to_8875e30`.

That choice is a strict improvement in fit. This target asks only for
`Nat.Prime` of each member; it never requires oddness. The `_odd_` child
proves the stronger statement with three extra `Odd` conjuncts, and has the
floor `9 ≤ n` rather than `7 ≤ n`. The child used here concludes
`Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r` with no parity
demand at all, which is exactly the target's conclusion, and its floor of `7`
is the true floor for this statement.

The split is again by magnitude: a finite certificate below
`8875694145621773516800000000000`, the unbounded Helfgott node above it. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  rcases lt_or_ge n 9 with hlt | hge
  · obtain ⟨k, hk⟩ := hodd
    have hn' : n = 2 * k + 1 := hk
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · have hn3 : n = 3 := by omega
      subst hn3
      exact WeakGoldbach.three_primes_three
    · rcases Nat.lt_or_ge n 7 with h7 | h7
      · have hn5 : n = 5 := by omega
        subst hn5
        exact WeakGoldbach.three_primes_five
      · have hn7 : n = 7 := by omega
        subst hn7
        exact WeakGoldbach.three_primes_of_prime 7 (by norm_num)
  · by_cases hhi : n ≤ 8875694145621773516800000000000
    · obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
        WeakGoldbach.verified_three_primes_to_8875e30 n (by omega) hhi hodd
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
    · obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
        WeakGoldbach.ternary_goldbach_helfgott_above_10pow27 n hodd (by omega)
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
