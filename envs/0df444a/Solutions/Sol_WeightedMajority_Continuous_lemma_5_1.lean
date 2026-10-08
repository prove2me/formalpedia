-- Prove2me | solution 1 for WeightedMajority.Continuous.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T21:52:59.008747+00:00
-- url     : https://prove2.me/submissions/b0b855f3-26c2-4226-a38c-d36fd4df9108

import Mathlib

/-- Lemma 5.1, p. 233: the factor interval in (5.1) is nonempty. -/
theorem solution (beta r : ℝ) (hbeta : 0 ≤ beta)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    beta ^ r ≤ 1 + r * (beta - 1) := by
  have h := rpow_one_add_le_one_add_mul_self (s := beta - 1) (by linarith) hr0 hr1
  simpa using h
