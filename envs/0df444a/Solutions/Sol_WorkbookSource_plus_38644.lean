-- Prove2me | solution 1 for WorkbookSource.plus_38644
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:46.871895+00:00
-- url     : https://prove2.me/submissions/9d1ab44b-bfe7-47a3-87cb-158db7cc2a0f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (t z h : ℝ) (hz : t < z) (hh : h > 0) : t^3 - 3 * t - 2 ≤ (t + h)^3 - 3 * (t + h) + 2   := by
  have h0 : 0 ≤ (4 : ℝ) * (1) * (1 - h/2)^2 := by positivity
  have h1 : 0 ≤ (3 : ℝ) * (h) * (h/2 + t)^2 := by positivity
  have h2 : 0 ≤ (1 : ℝ) * (h) * (1 - h/2)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (t z h : ℝ) (hz : t < z) (hh : h > 0), t^3 - 3 * t - 2 ≤ (t + h)^3 - 3 * (t + h) + 2) := @solution
#print axioms solution
