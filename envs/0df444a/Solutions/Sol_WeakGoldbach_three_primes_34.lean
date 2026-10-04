-- Prove2me | solution 34 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T05:41:09.016386+00:00
-- url     : https://prove2.me/submissions/fe8a905e-df87-42df-b6e9-8a5aead5698d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

Routes the whole non-base range through
"WeakGoldbach.ternary_goldbach_all_odd_ge_9", which is Helfgott's 2013
theorem (arXiv:1312.7748, Thm 1.1) at its sharp floor: every odd `n >= 9`
is a sum of three odd primes. This is settled mathematics, so the only Open
child is a statement the platform has not yet verified rather than an open
conjecture.

The floor is the reason the `Disproved` floor-5 variants exist: Helfgott with
floor `5 < n` is refuted at `n = 7` by `7 = 2 + 2 + 3`, and `3 + 3 + 3 = 9`
is the least all-odd sum. The target still has to cover `n = 7`, which no
`ge_9`-floored child reaches, so `n = 7` is discharged here by exhibiting
`2 + 2 + 3` directly. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  -- `key` repacks a three-prime equation into the target's multiset form.
  -- The equation is oriented `p + q + r = n` so the multiset sum closes by
  -- `simpa` alone, leaving no arithmetic obligation to discharge.
  have key : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r →
      (p + q + r = n) →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro p q r hp hq hr hsum
    refine ⟨{p, q, r}, by simp, ?_, ?_⟩
    · intro t ht
      simp only [Multiset.insert_eq_cons, Multiset.cons_zero, Multiset.mem_cons,
        Multiset.notMem_zero, Multiset.mem_singleton, or_false] at ht
      rcases ht with ht | ht | ht
      · simpa [ht] using hp
      · simpa [ht] using hq
      · simpa [ht] using hr
    · simpa [Multiset.sum_cons, Multiset.sum_zero, add_assoc] using hsum
  -- `Odd n` is opaque to `omega`: it is the atom `Odd n`, not a linear
  -- relation. Destruct it exactly once, here, into `hk : n = 2 * k + 1`, and
  -- keep `hk` so the child's `Odd n` hypothesis can be rebuilt later.
  obtain ⟨k, hk⟩ := hodd
  have hodd' : Odd n := ⟨k, hk⟩
  rcases Nat.lt_or_ge n 7 with hlt | hge
  · rcases Nat.lt_or_ge n 5 with h5 | h5
    · have hn3 : n = 3 := by omega
      simpa [hn3] using WeakGoldbach.three_primes_three
    · have hn5 : n = 5 := by omega
      simpa [hn5] using WeakGoldbach.three_primes_five
  · rcases Nat.lt_or_ge n 9 with h9 | h9
    · -- `7 <= n < 9` with `n = 2 * k + 1` pins `n = 7`, and `7 = 2 + 2 + 3`.
      have hn7 : n = 7 := by omega
      refine key 2 2 3 Nat.prime_two Nat.prime_two Nat.prime_three ?_
      omega
    · -- `9 <= n` and `Odd n` are exactly the child's hypotheses. Open the
      -- child's existential to get `p q r hp hq hr ... hpqr`, and drop its
      -- `Odd p`/`Odd q`/`Odd r` conclusions: the target asks only for
      -- primality of each summand.
      obtain ⟨p, q, r, hp, hq, hr, _hpo, _hqo, _hro, hpqr⟩ :=
        WeakGoldbach.ternary_goldbach_all_odd_ge_9 n h9 hodd'
      -- The child concludes `n = p + q + r`; `key` is stated with the sum on
      -- the left so that `simpa` alone closes the multiset obligation. Flip the
      -- orientation once, here, rather than re-deriving either side.
      have hpqr' : p + q + r = n := hpqr.symm
      refine key p q r hp hq hr hpqr'
