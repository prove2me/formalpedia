-- Prove2me | solution 1 for WorkbookSource.plus_71891
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:40:59.046225+00:00
-- url     : https://prove2.me/submissions/e806e372-9e09-40bf-a795-2324dcd01f4d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h1 : a^2 + b^2 - c^2 ≥ 0) (h2 : a^2 + c^2 - b^2 ≥ 0) (h3 : b^2 + c^2 - a^2 ≥ 0) : (a + b - c)^2 * (a + c - b)^2 ≥ (a^2 + b^2 - c^2) * (a^2 + c^2 - b^2)   := by
  have hw0 : 0 ≤ (a^2 + b^2 - c^2) := by linarith only [h1]
  have hw1 : 0 ≤ (a^2 - b^2 + c^2) := by linarith only [h2]
  have hw2 : 0 ≤ (-a^2 + b^2 + c^2) := by linarith only [h3]
  have hsum : 0 ≤ (2 : ℝ) * ((-a^2 + b^2 + c^2)) * (-b + c)^2 := by positivity
  have hid : ( (a + b - c)^2 * (a + c - b)^2 ) - ( (a^2 + b^2 - c^2) * (a^2 + c^2 - b^2)   ) = (2 : ℝ) * ((-a^2 + b^2 + c^2)) * (-b + c)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h1 : a^2 + b^2 - c^2 ≥ 0) (h2 : a^2 + c^2 - b^2 ≥ 0) (h3 : b^2 + c^2 - a^2 ≥ 0), (a + b - c)^2 * (a + c - b)^2 ≥ (a^2 + b^2 - c^2) * (a^2 + c^2 - b^2)) := @solution
#print axioms solution
