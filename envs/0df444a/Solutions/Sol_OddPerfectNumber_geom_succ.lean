-- Prove2me | solution 1 for OddPerfectNumber.geom_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:14:55.243466+00:00
-- url     : https://prove2.me/submissions/50a1dd4f-a6e5-47f7-897f-8528e5345768

import Mathlib

-- STAGED direct proof, verbatim from the accepted DHP toolkit
-- (solution 7809bdb2), republished standalone.
theorem solution (q n : Nat) :
    ∑ i ∈ Finset.range (n + 1), q ^ i = q * (∑ i ∈ Finset.range n, q ^ i) + 1 := by
  rw [Finset.sum_range_succ']
  simp [Finset.mul_sum, pow_succ, mul_comm]
