-- Prove2me | solution 1 for WorkbookSource.base_1730
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:10:41.138136+00:00
-- url     : https://prove2.me/submissions/b3be1d23-d3f0-4c48-a814-4b10991a7168

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y : ℝ) : 2 * (x + y) ^ 8 + x ^ 4 * y ^ 4 - x ^ 5 * y ^ 3 - x ^ 3 * y ^ 5 ≥ 0  := by
  have hsum : 0 ≤ (329/5 : ℝ) * (1) * (51*x^4/329 + 475*x^3*y/658 + x^2*y^2 + 475*x*y^3/658 + 51*y^4/329)^2 + (8623/6580 : ℝ) * (1) * (4190*x^4/8623 + x^3*y + x*y^3 + 4190*y^4/8623)^2 + (4718/43115 : ℝ) * (1) * (x^4 + y^4)^2 := by positivity
  have hid : ( 2 * (x + y) ^ 8 + x ^ 4 * y ^ 4 - x ^ 5 * y ^ 3 - x ^ 3 * y ^ 5 ) - ( 0  ) = (329/5 : ℝ) * (1) * (51*x^4/329 + 475*x^3*y/658 + x^2*y^2 + 475*x*y^3/658 + 51*y^4/329)^2 + (8623/6580 : ℝ) * (1) * (4190*x^4/8623 + x^3*y + x*y^3 + 4190*y^4/8623)^2 + (4718/43115 : ℝ) * (1) * (x^4 + y^4)^2 := by
    try simp only []
    ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ), 2 * (x + y) ^ 8 + x ^ 4 * y ^ 4 - x ^ 5 * y ^ 3 - x ^ 3 * y ^ 5 ≥ 0) := @solution
#print axioms solution
