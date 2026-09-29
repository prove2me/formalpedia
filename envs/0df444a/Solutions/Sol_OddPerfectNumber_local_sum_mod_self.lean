-- Prove2me | solution 1 for OddPerfectNumber.local_sum_mod_self
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:03:13.222581+00:00
-- url     : https://prove2.me/submissions/47082a38-6981-41be-a749-570168e2db24

import Mathlib

-- STAGED direct proof. Peel step verbatim from the accepted DHP toolkit
-- (geom_succ in solution 7809bdb2); mod steps per Mathlib usage.
-- NOTE (remote CE 7f463ff2): the _right mod-split variant only matches
-- addend-first form, but the peel yields multiple-first (r * X + 1), so
-- commute first and use the left variant (see regression test).
theorem solution (r a : Nat) (hr : r.Prime) :
    (∑ i ∈ Finset.range (2 * a + 1), r ^ i) % r = 1 := by
  have hpeel : (∑ i ∈ Finset.range (2 * a + 1), r ^ i)
      = r * (∑ i ∈ Finset.range (2 * a), r ^ i) + 1 := by
    rw [Finset.sum_range_succ']
    simp [Finset.mul_sum, pow_succ, mul_comm]
  rw [hpeel, add_comm _ 1, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hr.one_lt]
