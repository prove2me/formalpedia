-- Prove2me | solution 1 for WorkbookSource.base_43118
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:21:13.514373+00:00
-- url     : https://prove2.me/submissions/4ab8a90a-b9e9-4194-8083-76393804203a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution {a b c d : ℝ} :
  3 * a ^ 2 * d ^ 2 + 3 * b ^ 2 * c ^ 2 + 2 * a ^ 2 * c ^ 2 + 2 * b ^ 2 * d ^ 2 + 2 * a * b * c * d ≥ 3 * a ^ 2 * c * d + 3 * d ^ 2 * a * b + 3 * c ^ 2 * a * b + 3 * b ^ 2 * c * d  := by
  have h0 : 0 ≤ (3 : ℝ) * (-a*c/2 + b*c - b*d/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3 : ℝ) * (-a*c/2 + a*d - b*d/2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (1/2 : ℝ) * (-a*c + b*d)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2]
example : (∀ {a b c d : ℝ}, 3 * a ^ 2 * d ^ 2 + 3 * b ^ 2 * c ^ 2 + 2 * a ^ 2 * c ^ 2 + 2 * b ^ 2 * d ^ 2 + 2 * a * b * c * d ≥ 3 * a ^ 2 * c * d + 3 * d ^ 2 * a * b + 3 * c ^ 2 * a * b + 3 * b ^ 2 * c * d) := @solution
#print axioms solution
