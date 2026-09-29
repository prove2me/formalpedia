-- Prove2me | solution 1 for WorkbookSource.base_43507
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:23.855855+00:00
-- url     : https://prove2.me/submissions/c1a5f045-66c8-49bd-9422-c38b4898f0b4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (p q r : ℝ) : p ^ 4 * q ^ 2 + q ^ 4 * p ^ 2 + p ^ 4 * r ^ 2 + r ^ 4 * p ^ 2 + q ^ 4 * r ^ 2 + r ^ 4 * q ^ 2 ≥ 2 * (p ^ 3 * q ^ 3 + q ^ 3 * r ^ 3 + r ^ 3 * p ^ 3)  := by
  have h0 : 0 ≤ (1 : ℝ) * (-q^2*r + q*r^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (1 : ℝ) * (-p^2*r + p*r^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1 : ℝ) * (-p^2*q + p*q^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ (p q r : ℝ), p ^ 4 * q ^ 2 + q ^ 4 * p ^ 2 + p ^ 4 * r ^ 2 + r ^ 4 * p ^ 2 + q ^ 4 * r ^ 2 + r ^ 4 * q ^ 2 ≥ 2 * (p ^ 3 * q ^ 3 + q ^ 3 * r ^ 3 + r ^ 3 * p ^ 3)) := @solution
#print axioms solution
