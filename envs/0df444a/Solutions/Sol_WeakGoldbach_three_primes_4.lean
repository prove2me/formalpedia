-- Prove2me | solution 4 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T08:13:48.453261+00:00
-- url     : https://prove2.me/submissions/459a86f6-8adc-432a-a144-8762691ec494
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_goldbach_odd_variant

/-- Every odd natural `n > 1` is a sum of at most three primes.

This is a reduction of the `Multiset`-packaged weak Goldbach statement to the
three-witness analytic form `goldbach_odd_variant`, together with the finitely
many small values, which are covered by the Proved sibling theorems
`three_primes_three`, `three_primes_five` and `three_primes_of_prime`.

`hodd` is never destructured in the main goal, so `n` stays abstract and each
small case remains a concrete goal that the Proved siblings match exactly. Its
arithmetic content is recovered only *inside* the `hbig` sub-proof, so that
`omega` can use it without rewriting the surrounding goal. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have hnot2 : ¬ 2 ∣ n := hodd.not_two_dvd_nat
  by_cases hprime : Nat.Prime n
  · exact WeakGoldbach.three_primes_of_prime n hprime
  · by_cases h3 : n = 3
    · subst n
      exact WeakGoldbach.three_primes_three
    · by_cases h5 : n = 5
      · subst n
        exact WeakGoldbach.three_primes_five
      · by_cases h7 : n = 7
        · subst n
          refine ⟨({2, 2, 3} : Multiset ℕ), by simp, ?_, by norm_num⟩
          intro x hx
          -- `{2, 2, 3}` is notation sugar; `Multiset.insert_eq_cons` and
          -- `Multiset.cons_zero` (both `@[simp]`, `rfl`) unfold it to
          -- `2 ::ₘ 2 ::ₘ 3 ::ₘ 0`, after which `Multiset.mem_cons` and
          -- `Multiset.notMem_zero` reduce membership to a disjunction. The two
          -- duplicate `2` entries share one branch, and the final branch is a
          -- singleton `{3}`, so `Multiset.mem_singleton` is needed to turn the
          -- residual `x ∈ {3}` into the equation `x = 3`.
          simp only [Multiset.insert_eq_cons, Multiset.cons_zero,
            Multiset.mem_cons, Multiset.notMem_zero, Multiset.mem_singleton,
            or_false] at hx
          rcases hx with hx | hx | hx
          · subst hx
            exact Nat.prime_two
          · subst hx
            exact Nat.prime_two
          · subst hx
            exact Nat.prime_three
        · have hbig : 7 < n := by
            rcases hodd with ⟨k, hk⟩
            omega
          obtain ⟨p, q, r, hp, hq, hr, hsum⟩ := goldbach_odd_variant n hbig hnot2
          refine ⟨{p, q, r}, by simp, ?_, ?_⟩
          · intro x hx
            simp at hx
            rcases hx with hx | hx | hx
            · subst hx
              exact hp
            · subst hx
              exact hq
            · subst hx
              exact hr
          · have hval : p + q + r = n := hsum.symm
            simpa [Multiset.sum_cons, Multiset.sum_zero, add_assoc] using hval
