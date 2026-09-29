-- Prove2me | solution 1 for WorkbookSource.base_20583
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:22.818733+00:00
-- url     : https://prove2.me/submissions/3c5a3d82-0d96-4f61-800a-6611537becf0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b x y : ℝ) (h : x^2 + y^2 = 4) : (a + b)^2 - (x + a*y)*(x + b*y) + 4 ≥ 0  := by
  have hw0 : 0 ≤ (x^2 + y^2 - 4) := by linarith only [h]
  have hw1 : 0 ≤ (-x^2 - y^2 + 4) := by linarith only [h]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-a*x/2 - b*x/2 + y)^2 + (1/4 : ℝ) * (1) * (-a*y + b*y)^2 + (1 : ℝ) * ((-x^2 - y^2 + 4)) * (1)^2 + (1/4 : ℝ) * ((-x^2 - y^2 + 4)) * (a + b)^2 := by positivity
  have hid : ( (a + b)^2 - (x + a*y)*(x + b*y) + 4 ) - ( 0  ) = (1 : ℝ) * (1) * (-a*x/2 - b*x/2 + y)^2 + (1/4 : ℝ) * (1) * (-a*y + b*y)^2 + (1 : ℝ) * ((-x^2 - y^2 + 4)) * (1)^2 + (1/4 : ℝ) * ((-x^2 - y^2 + 4)) * (a + b)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b x y : ℝ) (h : x^2 + y^2 = 4), (a + b)^2 - (x + a*y)*(x + b*y) + 4 ≥ 0) := @solution
#print axioms solution
