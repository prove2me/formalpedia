-- Prove2me | solution 26 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T20:45:39.315376+00:00
-- url     : https://prove2.me/submissions/3b4a0904-a346-4138-a1e6-476b5ad5c756
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_9
import Theorems.Thm_WeakGoldbach_three_primes_of_prime

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

Repair of candidate 6450, whose only error group was `simp` made no progress
at the membership test. The multiset literal `{p, q, r}` elaborates to
`insert r (cons q (cons p nil))`, so `Multiset.mem_cons` alone does not fire;
`Multiset.insert_eq_cons` is the lemma that exposes the cons structure.

Repair of candidate 6461, whose only error group (E01, L20, UNSOLVED GOALS)
left `⊢ False` open in `case «0»` with context `k : ℕ`, `hk : n = 2 * 0 + 1`,
`hn' : n = 2 * 0 + 1`, `hlt' : 0 < 4`.  That context is exactly the `k = 0`
branch of `interval_cases k`: `hk` has collapsed to `n = 1`.  The branch is
genuinely dead, but not because `n = 1` is non-prime in the way the script
assumed — it is dead because the *hypothesis* `1 < n` rules it out.  The old
script ran `interval_cases k <;> norm_num [hn']`, and `norm_num` has no
clause that turns `hn' : n = 1` together with `hn : 1 < n` into `False`, so
the branch survived.

The fix splits the two jobs that were being asked of one tactic:
  * `norm_num [hn']` still proves `Nat.Prime n` in each of the `k = 1, 2, 3`
    branches, where `hn'` rewrites `n` to a literal prime.
  * the `k = 0` branch is closed by `omega`, which sees the linear
    contradiction `1 < n` against `n = 2 * 0 + 1` directly.

`<;>` keeps the application uniform, so both jobs run in every branch. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  rcases lt_or_ge n 9 with hlt | hge
  · -- `n < 9`, `Odd n` and `1 < n` leave exactly `n = 3, 5, 7`, all prime.
    obtain ⟨k, hk⟩ := hodd
    have hn' : n = 2 * k + 1 := hk
    have hlt' : k < 4 := by omega
    have hprime : Nat.Prime n := by
      interval_cases k <;> first
        | omega
        | norm_num [hn']
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
