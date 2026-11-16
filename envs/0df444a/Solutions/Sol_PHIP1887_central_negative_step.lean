-- Prove2me | solution 1 for PHIP1887.central_negative_step
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T17:43:53.791836+00:00
-- url     : https://prove2.me/submissions/824b1088-d0f3-4c35-a421-fba656a09da1

import Mathlib

theorem solution (k a b c : ℝ) (hk : 0 < k)
    (ha : a < 0) (hc : 0 ≤ c)
    (heq : c = k^2*a - 2*k*(2*k+1)*b) : b < 0 := by
  have hk2 : 0 < k^2 := sq_pos_of_pos hk
  have hka : k^2*a < 0 := mul_neg_of_pos_of_neg hk2 ha
  have hcoef : 0 ≤ 2*k*(2*k+1) := by positivity
  by_contra hn
  have hb : 0 ≤ b := le_of_not_gt hn
  have hp := mul_nonneg hcoef hb
  linarith

