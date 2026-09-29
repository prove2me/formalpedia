-- Prove2me | solution 1 for WorkbookSource.base_17570
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:29.052985+00:00
-- url     : https://prove2.me/submissions/7c4b0b35-e2ce-419c-baa1-27219ebd42a4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h1 : x + y + z = 1) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 4) : (y - z) * (x - y) ≤ 11 / 6  := by
  have hw0 : 0 ≤ (x + y + z - 1) := by linarith only [h1]
  have hw1 : 0 ≤ (-x - y - z + 1) := by linarith only [h1]
  have hw2 : 0 ≤ (x^2 + y^2 + z^2 - 4) := by linarith only [h2]
  have hw3 : 0 ≤ (-x^2 - y^2 - z^2 + 4) := by linarith only [h2]
  have hsum : 0 ≤ (3/2 : ℝ) * (1) * (-x/3 + y - z/3 - 1/9)^2 + (1/3 : ℝ) * (1) * (x + z - 2/3)^2 + (1/2 : ℝ) * ((-x^2 - y^2 - z^2 + 4)) * (1)^2 + (1/3 : ℝ) * ((x + y + z - 1)) * (1)^2 := by positivity
  have hid : ( 11 / 6  ) - ( (y - z) * (x - y) ) = (3/2 : ℝ) * (1) * (-x/3 + y - z/3 - 1/9)^2 + (1/3 : ℝ) * (1) * (x + z - 2/3)^2 + (1/2 : ℝ) * ((-x^2 - y^2 - z^2 + 4)) * (1)^2 + (1/3 : ℝ) * ((x + y + z - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h1 : x + y + z = 1) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 4), (y - z) * (x - y) ≤ 11 / 6) := @solution
#print axioms solution
