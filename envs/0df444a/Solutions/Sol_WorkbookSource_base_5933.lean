-- Prove2me | solution 1 for WorkbookSource.base_5933
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:43:30.37297+00:00
-- url     : https://prove2.me/submissions/40d8e42b-e3ae-45dd-8d79-4803aaaa52fa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : a^2 + b^2 ≤ 1) :
  (a * c + b * d - 1)^2 ≥ (a^2 + b^2 - 1) * (c^2 + d^2 - 1)  := by
  have hw0 : 0 ≤ (-a^2 - b^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-a^2 + a*c - b^2 + b*d)^2 + (1 : ℝ) * ((-a^2 - b^2 + 1)) * (-b + d)^2 + (1 : ℝ) * ((-a^2 - b^2 + 1)) * (-a + c)^2 := by positivity
  have hid : (
  (a * c + b * d - 1)^2 ) - ( (a^2 + b^2 - 1) * (c^2 + d^2 - 1)  ) = (1 : ℝ) * (1) * (-a^2 + a*c - b^2 + b*d)^2 + (1 : ℝ) * ((-a^2 - b^2 + 1)) * (-b + d)^2 + (1 : ℝ) * ((-a^2 - b^2 + 1)) * (-a + c)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : a^2 + b^2 ≤ 1), (a * c + b * d - 1)^2 ≥ (a^2 + b^2 - 1) * (c^2 + d^2 - 1)) := @solution
#print axioms solution
