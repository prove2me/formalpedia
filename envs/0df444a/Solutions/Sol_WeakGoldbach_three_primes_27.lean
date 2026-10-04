-- Prove2me | solution 27 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T21:49:32.339137+00:00
-- url     : https://prove2.me/submissions/ff38aa10-1cff-463f-ae06-45ad607db518
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

Repair of candidate 6484, whose CE reported two independent TYPE_MISMATCH
groups at lines 31 and 34. Both had the same cause: the branch proved
`hn3 : n = 3` (resp. `hn5 : n = 5`) with `omega` but never used it, so the
goal still read `s.sum = n` while `three_primes_three` (resp.
`three_primes_five`) delivers `s.sum = 3` (resp. `s.sum = 5`).

The `n = 7` branch of 6484 was already correct precisely because it did
`subst hn7`; this repair makes the two sibling branches follow that same
mechanism, so all three small values are discharged the same way. -/
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
