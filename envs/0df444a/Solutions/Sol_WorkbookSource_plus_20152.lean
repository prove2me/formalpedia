-- Prove2me | solution 1 for WorkbookSource.plus_20152
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:41.343643+00:00
-- url     : https://prove2.me/submissions/d6e3d13c-4b7e-47e6-aab6-4e72b5c35e5b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a * b * (a + b) ^ 2 + 2 * c ^ 4 ≥ 2 * a * b * c * (b + c + a)   := by
  have h0 : 0 ≤ (2 : ℝ) * (1) * (-a*b + c^2)^2 := by positivity
  have h1 : 0 ≤ (2 : ℝ) * (a*b) * (-a/2 - b/2 + c)^2 := by positivity
  have h2 : 0 ≤ (1/2 : ℝ) * (a*b) * (-a + b)^2 := by positivity
  nlinarith only [h0, h1, h2]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), a * b * (a + b) ^ 2 + 2 * c ^ 4 ≥ 2 * a * b * c * (b + c + a)) := @solution
#print axioms solution
