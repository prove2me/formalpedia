-- Prove2me | solution 1 for WorkbookSource.base_53551
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:28.812039+00:00
-- url     : https://prove2.me/submissions/4cc24d36-0336-48c9-a819-105305a5f81f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b : ℝ) : 4 * (a + b) ^ 2 * (a ^ 2 + b ^ 2) ^ 2 - 25 * (a ^ 2 + b ^ 2) * (25 * a ^ 4 - 4 * a ^ 3 * b - 31 * a ^ 2 * b ^ 2 - 4 * a * b ^ 3 + 25 * b ^ 4) ≤ 0  := by
  have h0 : 0 ≤ (621 : ℝ) * (-787*a^3/3795 - 5450*a^2*b/36639 - 2*a*b^2/23 + b^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (41347968/69575 : ℝ) * (a^3 - 225225275*a^2*b/1829647584 - 106288105*a*b^2/609882528)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (734569/8995767288 : ℝ) * (18505877*a^2*b/121203885 + a*b^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (16656196606/208845808224075 : ℝ) * (a^2*b)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3]
example : (∀ (a b : ℝ), 4 * (a + b) ^ 2 * (a ^ 2 + b ^ 2) ^ 2 - 25 * (a ^ 2 + b ^ 2) * (25 * a ^ 4 - 4 * a ^ 3 * b - 31 * a ^ 2 * b ^ 2 - 4 * a * b ^ 3 + 25 * b ^ 4) ≤ 0) := @solution
#print axioms solution
