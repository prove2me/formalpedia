-- Prove2me | solution 1 for WorkbookSource.base_34479
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:26.239107+00:00
-- url     : https://prove2.me/submissions/00cd49ff-4109-41e9-a4be-7ef901a608e0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h1 : x + y + z = 2) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 6) : (y - z) * (x + y) ≤ 9  := by
  have hw0 : 0 ≤ (x + y + z - 2) := by linarith only [h1]
  have hw1 : 0 ≤ (-x - y - z + 2) := by linarith only [h1]
  have hw2 : 0 ≤ (x^2 + y^2 + z^2 - 6) := by linarith only [h2]
  have hw3 : 0 ≤ (-x^2 - y^2 - z^2 + 6) := by linarith only [h2]
  have hsum : 0 ≤ (3/2 : ℝ) * (1) * (x/3 + y/3 + z)^2 + (4/3 : ℝ) * (1) * (x - y/2)^2 + (3/2 : ℝ) * ((-x^2 - y^2 - z^2 + 6)) * (1)^2 := by positivity
  have hid : ( 9  ) - ( (y - z) * (x + y) ) = (3/2 : ℝ) * (1) * (x/3 + y/3 + z)^2 + (4/3 : ℝ) * (1) * (x - y/2)^2 + (3/2 : ℝ) * ((-x^2 - y^2 - z^2 + 6)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h1 : x + y + z = 2) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 6), (y - z) * (x + y) ≤ 9) := @solution
#print axioms solution
