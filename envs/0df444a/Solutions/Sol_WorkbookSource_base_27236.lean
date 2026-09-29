-- Prove2me | solution 1 for WorkbookSource.base_27236
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:36:03.336186+00:00
-- url     : https://prove2.me/submissions/65f56057-a18c-47bc-9a40-411b2128ec5f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution {x y z a b c : ℝ} (hx : x = 2 * a - b) (hy : y = 2 * b - c) (hz : z = 2 * c - a) : 3 * (x ^ 4 + y ^ 4 + z ^ 4 - x ^ 3 * y - y ^ 3 * z - z ^ 3 * x) ≥ x ^ 2 * (y - z) ^ 2 + y ^ 2 * (z - x) ^ 2 + z ^ 2 * (x - y) ^ 2  := by
  have helim : b = (2*a - x) := by linarith only [hx]
  have hsum : 0 ≤ (3 : ℝ) * (-x^2/2 + x*y/2 - x*z/2 - y^2/2 + z^2)^2 + (9/4 : ℝ) * (-x^2 + x*y/3 + x*z/3 + y^2 - 2*y*z/3)^2 := by positivity
  have hid : ( 3 * (x ^ 4 + y ^ 4 + z ^ 4 - x ^ 3 * y - y ^ 3 * z - z ^ 3 * x) ) - ( x ^ 2 * (y - z) ^ 2 + y ^ 2 * (z - x) ^ 2 + z ^ 2 * (x - y) ^ 2  ) = (3 : ℝ) * (-x^2/2 + x*y/2 - x*z/2 - y^2/2 + z^2)^2 + (9/4 : ℝ) * (-x^2 + x*y/3 + x*z/3 + y^2 - 2*y*z/3)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ {x y z a b c : ℝ} (hx : x = 2 * a - b) (hy : y = 2 * b - c) (hz : z = 2 * c - a), 3 * (x ^ 4 + y ^ 4 + z ^ 4 - x ^ 3 * y - y ^ 3 * z - z ^ 3 * x) ≥ x ^ 2 * (y - z) ^ 2 + y ^ 2 * (z - x) ^ 2 + z ^ 2 * (x - y) ^ 2) := @solution
#print axioms solution
