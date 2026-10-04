-- Prove2me | solution 22 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T16:37:19.947105+00:00
-- url     : https://prove2.me/submissions/c2141c0c-b1f7-4130-adcd-9e7bf1af3aa7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_of_prime
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_strong_goldbach_conjecture

set_option autoImplicit false

/-- Every odd natural `n > 1` is a sum of at most three primes.

This reduces the target to a single Open dependency rather than a partition
of the range into several analytic bands.

The observation is that this target imposes NO oddness condition on the
summands, so for an odd `n` one may peel off the single prime 3 and ask only
that the even remainder `n - 3` be a sum of two primes. For odd `n >= 7` the
number `n - 3` is even and at least 4, so it satisfies both hypotheses of
`strong_goldbach_conjecture` (`4 <= m` and `2 | m`), whose conclusion
`m = p + q` yields `n = 3 + p + q` as a sum of three primes.

The small odd values are discharged by the Proved value theorems, and every
prime `n` is settled directly by the Proved `three_primes_of_prime`. -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have three : ∀ (p q r : ℕ), Nat.Prime p → Nat.Prime q → Nat.Prime r → p + q + r = n →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ x ∈ s, Nat.Prime x) ∧ s.sum = n := by
    intro p q r hpq hqr hrs heq
    refine ⟨{p, q, r}, by simp, ?_, ?_⟩
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.cons_zero, Multiset.mem_cons,
        Multiset.notMem_zero, Multiset.mem_singleton, or_false] at hx
      rcases hx with hx | hx | hx
      · simpa [hx] using hpq
      · simpa [hx] using hqr
      · simpa [hx] using hrs
    · have hval : p + q + r = n := heq
      simpa [Multiset.sum_cons, Multiset.sum_zero, add_assoc] using hval
  -- `Odd n` exhibits `n = 2 * k + 1`. Working with `k` rather than `n - 3`
  -- keeps every later obligation plain linear arithmetic on `k`, with no
  -- truncated `Nat` subtraction anywhere in the proof.
  obtain ⟨k, hk⟩ := hodd
  -- Split off the odd values below 7, where `n - 3 < 4` and the Goldbach
  -- floor fails. This split is what makes the later bounds derivable.
  -- This is exactly the shape candidate 6403 proved for omega: from
  -- `1 < n`, `n = 2 * k + 1` and oddness alone, omega exhibits the
  -- disjunction directly, so no `Nat.lt_or_le` / `Nat.lt_trichotomy`
  -- combinator is needed and no branch order has to be matched by hand.
  have hodd9 : n = 3 ∨ n = 5 ∨ n = 7 ∨ 9 ≤ n := by omega
  rcases hodd9 with h3 | h5 | h7 | h9
  · -- `n = 3`: the Proved value theorem for the prime 3.
    subst h3
    exact WeakGoldbach.three_primes_three
  · -- `n = 5`: the Proved value theorem for the prime 5.
    subst h5
    exact WeakGoldbach.three_primes_five
  · -- `n = 7 = 2 + 2 + 3`, an explicit three-prime decomposition.
    refine three 2 2 3 (by decide) (by decide) Nat.prime_three ?_
    omega
  · have hn9 : 9 ≤ n := h9
    -- `n = 2 * k + 1` and `9 <= n` give `k >= 4`, so `2 * (k - 1) >= 6 >= 4`
    -- and `n = 3 + 2 * (k - 1)` with no truncated subtraction to reason about.
    have hk4 : 4 ≤ k := by omega
    have heven : (2 : ℕ) ∣ 2 * (k - 1) := ⟨k - 1, rfl⟩
    have h4 : 4 ≤ 2 * (k - 1) := by omega
    have hn3 : n = 3 + 2 * (k - 1) := by omega
    by_cases hprime : Nat.Prime n
    · exact WeakGoldbach.three_primes_of_prime n hprime
    · obtain ⟨p, q, hp, hq, heq⟩ := strong_goldbach_conjecture (2 * (k - 1)) h4 heven
      refine three 3 p q Nat.prime_three hp hq ?_
      -- `heq : 2 * (k - 1) = p + q`; `hn3` is the `n = 3 + 2 * (k - 1)` side.
      -- The helper wants `3 + p + q = n`, so this is pure linear arithmetic.
      omega

