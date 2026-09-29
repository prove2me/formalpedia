-- Prove2me | solution 1 for WorkbookSource.plus_61283
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:20:08.967891+00:00
-- url     : https://prove2.me/submissions/6610c4b9-e6bf-4acb-b767-188071d94330

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution {x y z : ℝ} (hx : 7 / 5 * z ≤ x + y) (hy : 7 / 5 * x ≤ y + z) (hz : 7 / 5 * y ≤ z + x) : (x ^ 2 + y ^ 2 + z ^ 2) * x * y * z - 1 / 9 * (x + y + z) * (x * y + y * z + z * x) ^ 2 ≥ 0   := by
  have hw0 : 0 ≤ (x + y - 7*z/5) := by linarith only [hx]
  have hw1 : 0 ≤ (-7*x/5 + y + z) := by linarith only [hy]
  have hw2 : 0 ≤ (x - 7*y/5 + z) := by linarith only [hz]
  have hsum : 0 ≤ (5/18 : ℝ) * ((x - 7*y/5 + z)) * (-x*y + y*z)^2 + (5/18 : ℝ) * ((-7*x/5 + y + z)) * (-x*y + x*z)^2 + (5/18 : ℝ) * ((x + y - 7*z/5)) * (-x*z + y*z)^2 := by positivity
  have hid : ( (x ^ 2 + y ^ 2 + z ^ 2) * x * y * z - 1 / 9 * (x + y + z) * (x * y + y * z + z * x) ^ 2 ) - ( 0   ) = (5/18 : ℝ) * ((x - 7*y/5 + z)) * (-x*y + y*z)^2 + (5/18 : ℝ) * ((-7*x/5 + y + z)) * (-x*y + x*z)^2 + (5/18 : ℝ) * ((x + y - 7*z/5)) * (-x*z + y*z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ {x y z : ℝ} (hx : 7 / 5 * z ≤ x + y) (hy : 7 / 5 * x ≤ y + z) (hz : 7 / 5 * y ≤ z + x), (x ^ 2 + y ^ 2 + z ^ 2) * x * y * z - 1 / 9 * (x + y + z) * (x * y + y * z + z * x) ^ 2 ≥ 0) := @solution
#print axioms solution
