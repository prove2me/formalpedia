-- Prove2me | solution 1 for WorkbookSource.base_54067
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:10.078782+00:00
-- url     : https://prove2.me/submissions/25d6f58b-911d-4f1b-a33b-050aaf5e6b7c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h : x + y + z = 3) :
  (x * y + y * z + z * x) ^ 2 + 3 ≥ 12 * x * y * z  := by
  have helim : z = (-x - y + 3) := by linarith only [h]
  have hsum : 0 ≤ (29/3 : ℝ) * (5*x^2/29 - 5*x*y/29 - 20*x/29 - 9*y^2/29 + y)^2 + (147/29 : ℝ) * (-23*x^2/63 - 5*x*y/9 + x - 5*y^2/63)^2 + (3 : ℝ) * (-x^2/9 - 7*x*y/9 - y^2/9 + 1)^2 := by positivity
  have hid : (
  (x * y + y * z + z * x) ^ 2 + 3 ) - ( 12 * x * y * z  ) = (29/3 : ℝ) * (5*x^2/29 - 5*x*y/29 - 20*x/29 - 9*y^2/29 + y)^2 + (147/29 : ℝ) * (-23*x^2/63 - 5*x*y/9 + x - 5*y^2/63)^2 + (3 : ℝ) * (-x^2/9 - 7*x*y/9 - y^2/9 + 1)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h : x + y + z = 3), (x * y + y * z + z * x) ^ 2 + 3 ≥ 12 * x * y * z) := @solution
#print axioms solution
