-- Prove2me | solution 33 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T01:54:11.023935+00:00
-- url     : https://prove2.me/submissions/5cc4083f-9d81-404e-afba-1c006ca39309
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_strong_goldbach_conjecture

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

Third distinct peel-off route, and the only one that routes the *entire*
non-base range through a single unbounded child.

Candidates 5277 and 6425 also import `strong_goldbach_conjecture`, but both
retain the guard `Nat.Prime n -> three_primes_of_prime n` in front.
`three_primes_of_prime` is a direct child of the target whose own graph points
back at this target through a sketch edge, so that guard makes the candidate's
dependency closure strictly larger than necessary. This one drops it: the
statement asks only for `Nat.Prime` of each summand and never requires
oddness, so there is no case in which an odd prime `n` needs special treatment
-- `n = 3 + p + q` discharges it uniformly.

The result is a two-child decomposition (`strong_goldbach_conjecture` plus the
two Proved base cases) with no Open child beyond that single node. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  -- `key` repacks a two-prime equation into the target's multiset form. The
  -- equation is oriented as `p + q + 3 = n` so the multiset sum closes by
  -- `simpa` alone, with no arithmetic obligation left to discharge.
  have key : ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → (p + q + 3 = n) →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro p q hp hq hsum
    refine ⟨{p, q, 3}, by simp, ?_, ?_⟩
    · intro t ht
      simp only [Multiset.insert_eq_cons, Multiset.cons_zero, Multiset.mem_cons,
        Multiset.notMem_zero, Multiset.mem_singleton, or_false] at ht
      rcases ht with ht | ht | ht
      · simpa [ht] using hp
      · simpa [ht] using hq
      · simpa [ht] using Nat.prime_three
    · simpa [Multiset.sum_cons, Multiset.sum_zero, add_assoc] using hsum
  -- `Odd n` is opaque to `omega`: it is an atom, not a linear relation. Expose
  -- it once, up front, as the linear equation `n = 2 * k + 1`, so that every
  -- later arithmetic obligation has a usable constraint. Doing this before the
  -- case split is what lets `omega` pin down the two small values.
  obtain ⟨k, hk⟩ := hodd
  rcases Nat.lt_or_ge n 7 with hlt | hge
  · rcases Nat.lt_or_ge n 5 with h5 | h5
    · have hn3 : n = 3 := by omega
      simpa [hn3] using WeakGoldbach.three_primes_three
    · have hn5 : n = 5 := by omega
      simpa [hn5] using WeakGoldbach.three_primes_five
  · -- `Odd n` is opaque to `omega`, so expose it as the linear equation
    -- `n = 2 * k + 1`. With `n >= 7` this gives `n - 3 = (k - 1) + (k - 1)`,
    -- so the residual is even and at least `4` -- exactly the two hypotheses
    -- `strong_goldbach_conjecture` requires.
    have hge3 : 3 ≤ n := by omega
    have hsub : 4 ≤ n - 3 := by omega
    have heven : 2 ∣ n - 3 := by omega
    obtain ⟨p, q, hp, hq, hpq⟩ :=
      strong_goldbach_conjecture (n - 3) hsub heven
    have hsum : p + q + 3 = n := calc
      p + q + 3 = (n - 3) + 3 := by rw [hpq]
      _ = n := Nat.sub_add_cancel hge3
    exact key p q hp hq hsum
