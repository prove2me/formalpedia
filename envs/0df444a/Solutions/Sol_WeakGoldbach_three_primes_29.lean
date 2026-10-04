-- Prove2me | solution 29 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T22:40:20.079524+00:00
-- url     : https://prove2.me/submissions/35eda95c-0968-4922-a9c9-719d1eb39d25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_goldbach_odd_variant

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

Materially different dependency shape from candidates 6469/6472/6495/6497.
Those reduce the large case through `ternary_goldbach_all_odd_ge_9`, whose
conclusion additionally demands `Odd p`, `Odd q`, `Odd r`. This target does
not: it asks only for `Nat.Prime` of each member. `goldbach_odd_variant`
states exactly the needed conclusion, under the assumption `¬ 2 ∣ n` rather
than `Odd n`, and is the correct bridge for it.

The small cases keep the verified `subst` mechanism from 6495. -/
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
  · obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
      goldbach_odd_variant n (by omega) (by
        obtain ⟨k, hk⟩ := hodd
        omega)
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
