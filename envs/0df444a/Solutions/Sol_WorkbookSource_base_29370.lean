-- Prove2me | solution 1 for WorkbookSource.base_29370
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:47:46.648341+00:00
-- url     : https://prove2.me/submissions/e3a787fc-e1da-480d-9bc8-aeed1d702771

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : (y - z) ^ 2 * (x ^ 2 - x + 1) + (z - x) ^ 2 * (y ^ 2 - y + 1) + (x - y) ^ 2 * (z ^ 2 - z + 1) ≥ 3 * (x - y) * (y - z) * (z - x)  := by
  have h0 : 0 ≤ (2 : ℝ) * (x*y/2 + x*z/2 - x/2 - y*z - y/2 + z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3/2 : ℝ) * (-x*y + x*z - x + y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (x y z : ℝ), (y - z) ^ 2 * (x ^ 2 - x + 1) + (z - x) ^ 2 * (y ^ 2 - y + 1) + (x - y) ^ 2 * (z ^ 2 - z + 1) ≥ 3 * (x - y) * (y - z) * (z - x)) := @solution
#print axioms solution
