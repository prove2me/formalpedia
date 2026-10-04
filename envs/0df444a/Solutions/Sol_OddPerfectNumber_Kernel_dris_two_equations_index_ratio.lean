-- Prove2me | solution 1 for OddPerfectNumber.Kernel.dris_two_equations_index_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T21:07:25.094248+00:00
-- url     : https://prove2.me/submissions/f48debeb-c263-4655-b202-41ed7f3a7546

-- Target: OddPerfectNumber.Kernel.dris_two_equations_index_ratio
-- c2fcb4c1-9a21-498d-8f8d-a74f682d9baa
--
-- From h1 : 2 m^2 = sigma(p^5) * s  and  h2 : sigma(m^2) = p^5 * s, the index cancels.
--
-- DIAGNOSTIC HISTORY (candidate 6730, 4 groups, all from ONE cause).  The report shows that
-- after `set A := (∑ d ∈ (p ^ 5).divisors, d) with hA` the context ALREADY contains
--
--     h1 : 2 * m ^ 2 = A * s
--     h2 : B = p ^ 5 * s
--
-- i.e. `set` REPLACED the sums inside the hypotheses, so my `rw [← hA]` and `rw [← hB]` had
-- nothing to match ("Did not find an occurrence of the pattern").  That is the sole cause:
--   L22 `rw [← hA]` in `2 * m ^ 2 = A * s`   -- h1 is ALREADY this goal.
--   L23 `rw [← hB]` in `B = p ^ 5 * s`       -- h2 is ALREADY this goal.
--   L29 `h2' has type B = p ^ 5 * s but expected A * (p^5 * s) = A * B`
--       -- the calc step needs `h2'` after reassociation, not before.
--   L32 `rw [← hB]` in `B * A = ...`         -- the goal is in `A`, `B` shape already.
-- THE REPAIR removes all four redundant rewrites: `h1` and `h2` are used directly in the `A`,
-- `B` language, and the closing step is an explicit `calc` with `simpa [Nat.mul_comm]` instead
-- of a `rw` into the goal.

import Mathlib

theorem solution (p m s : Nat)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    (∑ d ∈ (m ^ 2).divisors, d) * (∑ d ∈ (p ^ 5).divisors, d) =
      2 * p ^ 5 * m ^ 2 := by
  -- `set` substitutes the sums in the hypotheses too, so `h1` and `h2` are ALREADY in the
  -- abbreviated language; no `rw` is needed (candidate 6730 reported four such failures).
  set A := (∑ d ∈ (p ^ 5).divisors, d) with hA
  set B := (∑ d ∈ (m ^ 2).divisors, d) with hB
  have h1' : 2 * m ^ 2 = A * s := h1
  have h2' : B = p ^ 5 * s := h2
  -- Eliminate the index: multiply `h1'` by `p^5`, then rewrite `p^5 * s` with `h2'`.
  calc
    B * A = (p ^ 5 * s) * A := by rw [h2']
    _ = p ^ 5 * (A * s) := by ring
    _ = p ^ 5 * (2 * m ^ 2) := by rw [h1']
    _ = 2 * p ^ 5 * m ^ 2 := by ring
