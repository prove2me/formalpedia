-- Prove2me | solution 1 for WorkbookSource.base_26591
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:41.980998+00:00
-- url     : https://prove2.me/submissions/c0196139-b6d3-4fe4-b461-3d4a3f2d723f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : -(x + y + z)*x*y*z + x^4 + y*z*(y^2 + z^2) ≥ 0  := by
  have h0 : 0 ≤ (1 : ℝ) * (1) * (-x^2 + y*z)^2 := by positivity
  have h1 : 0 ≤ (1 : ℝ) * (y*z) * (-x/2 - y/2 + z)^2 := by positivity
  have h2 : 0 ≤ (3/4 : ℝ) * (y*z) * (-x + y)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), -(x + y + z)*x*y*z + x^4 + y*z*(y^2 + z^2) ≥ 0) := @solution
#print axioms solution
