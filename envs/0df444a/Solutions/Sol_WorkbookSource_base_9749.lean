-- Prove2me | solution 1 for WorkbookSource.base_9749
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:44.64697+00:00
-- url     : https://prove2.me/submissions/22be4cad-6531-4822-995f-d570cc48f012

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 3 * x ^ 2 + y ^ 2 + 1 ≥ 6 / 5 * (x ^ 2 + x * y + 2 * x)  := by
  have hn : 0 ≤ (9*x^2 - 6*x*y - 12*x + 5*y^2 + 5) := by
    have hs0 : 0 ≤ (9 : ℝ) * (1) * (x - y/3 - 2/3)^2 := by positivity
    have hs1 : 0 ≤ (4 : ℝ) * (1) * (y - 1/2)^2 := by positivity
    nlinarith only [hs0, hs1]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), 3 * x ^ 2 + y ^ 2 + 1 ≥ 6 / 5 * (x ^ 2 + x * y + 2 * x)) := @solution
#print axioms solution
