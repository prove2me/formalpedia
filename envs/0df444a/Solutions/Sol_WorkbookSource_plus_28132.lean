-- Prove2me | solution 1 for WorkbookSource.plus_28132
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:34.142362+00:00
-- url     : https://prove2.me/submissions/82fa8898-85f3-43f9-ba2b-6c380b5cd6c6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c x y z : ℝ) (ha : a + b + c = x + y + z) : a * x + b * y + c * z + (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) / 3 ≥ a * b + b * c + c * a   := by
  have helim : z = (a + b + c - x - y) := by linarith only [ha]
  have hsum : 0 ≤ (4/3 : ℝ) * (a/4 + b/4 + c - 3*x/4 - 3*y/4)^2 + (1/4 : ℝ) * (-a + b - x + y)^2 := by positivity
  have hid : ( a * x + b * y + c * z + (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) / 3 ) - ( a * b + b * c + c * a   ) = (4/3 : ℝ) * (a/4 + b/4 + c - 3*x/4 - 3*y/4)^2 + (1/4 : ℝ) * (-a + b - x + y)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c x y z : ℝ) (ha : a + b + c = x + y + z), a * x + b * y + c * z + (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) / 3 ≥ a * b + b * c + c * a) := @solution
#print axioms solution
