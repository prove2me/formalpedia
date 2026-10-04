-- Prove2me | solution 28 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T21:50:14.870497+00:00
-- url     : https://prove2.me/submissions/47ce9b4c-23b2-408b-a485-7f2f76ca09fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

Second repair of candidate 6484, differing from `sol_6484a.lean` in the
cause-linked part: the small-value branches close the definitional gap with
`simpa [hn]` instead of `subst hn`. The equality `hn : n = 3` is retained in
the context and used to rewrite the goal, so the substitution is reversible
and no hypothesis is consumed. Everything else is held identical to 6484 so
that any difference in the remote verdict is attributable to this mechanism
alone. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  rcases lt_or_ge n 9 with hlt | hge
  · obtain ⟨k, hk⟩ := hodd
    have hn' : n = 2 * k + 1 := hk
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · have hn3 : n = 3 := by omega
      simpa [hn3] using WeakGoldbach.three_primes_three
    · rcases Nat.lt_or_ge n 7 with h7 | h7
      · have hn5 : n = 5 := by omega
        simpa [hn5] using WeakGoldbach.three_primes_five
      · have hn7 : n = 7 := by omega
        simpa [hn7] using WeakGoldbach.three_primes_of_prime 7 (by norm_num)
  · obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
      WeakGoldbach.ternary_goldbach_all_odd_ge_9 n hge hodd
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
