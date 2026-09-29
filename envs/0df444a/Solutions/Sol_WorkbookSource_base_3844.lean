-- Prove2me | solution 1 for WorkbookSource.base_3844
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:40:54.946109+00:00
-- url     : https://prove2.me/submissions/a485fa75-8fd5-4b64-a34c-1c930c63f01a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) : 3 * (x^3 * y + y^3 * z + z^3 * x) ≤ (x + y + z) * (x^3 + y^3 + z^3)  := by
  have h0 : 0 ≤ (1 : ℝ) * (-x^2/2 + x*y/2 - x*z - y^2/2 + y*z/2 + z^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (3/4 : ℝ) * (x^2 - x*y - y^2 + y*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ (x y z : ℝ), 3 * (x^3 * y + y^3 * z + z^3 * x) ≤ (x + y + z) * (x^3 + y^3 + z^3)) := @solution
#print axioms solution
