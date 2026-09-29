-- Prove2me | solution 1 for WorkbookSource.base_15608
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:29.727643+00:00
-- url     : https://prove2.me/submissions/30df44f6-f0da-44df-b568-d46b5a8dc54a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) :  x ^ 4 + y ^ 4 + z ^ 4 + 1 / 27 ≥ 2 / 3 * (x * y + y * z + z * x) ^ 2  := by
  have helim : z = (-x - y + 1) := by linarith only [h]
  have hsum : 0 ≤ (37/9 : ℝ) * (-15*x^2/37 - 27*x*y/37 + 35*x/37 - 12*y^2/37 + y - 18/37)^2 + (100/111 : ℝ) * (13*x^2/40 + 2*x*y/5 - 9*x/20 + y^2 - 1/24)^2 + (9/16 : ℝ) * (x^2 + 2*x/3 - 1/3)^2 := by positivity
  have hid : (  x ^ 4 + y ^ 4 + z ^ 4 + 1 / 27 ) - ( 2 / 3 * (x * y + y * z + z * x) ^ 2  ) = (37/9 : ℝ) * (-15*x^2/37 - 27*x*y/37 + 35*x/37 - 12*y^2/37 + y - 18/37)^2 + (100/111 : ℝ) * (13*x^2/40 + 2*x*y/5 - 9*x/20 + y^2 - 1/24)^2 + (9/16 : ℝ) * (x^2 + 2*x/3 - 1/3)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1), x ^ 4 + y ^ 4 + z ^ 4 + 1 / 27 ≥ 2 / 3 * (x * y + y * z + z * x) ^ 2) := @solution
#print axioms solution
