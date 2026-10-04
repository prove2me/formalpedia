-- Prove2me | solution 30 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T23:41:55.976256+00:00
-- url     : https://prove2.me/submissions/d2e265c8-bc18-4745-94be-a49865496bfe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_ternary_goldbach_helfgott_above_10pow27
import Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

A two-child hybrid, structurally different from every accepted candidate so
far. Those rest on a single Open child covering the whole range above its
floor (`ternary_goldbach_all_odd_ge_9` for 6495/6497, `goldbach_odd_variant`
for 6518). This one splits the large case by magnitude instead:

* `n ≤ 8875694145621773516800000000000` uses
  `verified_three_odd_primes_to_8875e30`, which is a *finite* certificate
  covering the whole low range in one child.
* `n` above that bound uses `ternary_goldbach_helfgott_above_10pow27`, which
  is unbounded above. (Its floor `10 ^ 27` is irrelevant here: this branch is
  reached only for `n > 8.87 * 10^30 > 10 ^ 27`.)

The two ranges are disjoint and exhaustive, so no residue class of odd `n` is
left without a child, and each child is used strictly inside the range it can
actually discharge.

Small values keep the SKETCH_ACCEPTED `subst` mechanism of candidate 6495. -/
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
    · obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
        WeakGoldbach.verified_three_odd_primes_to_8875e30 n hge hhi hodd
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
