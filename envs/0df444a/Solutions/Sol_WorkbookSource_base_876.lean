-- Prove2me | solution 1 for WorkbookSource.base_876
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:18:45.20139+00:00
-- url     : https://prove2.me/submissions/a4b93b3e-91ba-48b6-b0dd-a2df199f8720

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 3 ≥ (27 / 4) * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a)  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hsum : 0 ≤ (4 : ℝ) * ((c)) * (a + b/4 - c/2)^2 + (4 : ℝ) * ((b)) * (a/4 - b/2 + c)^2 + (4 : ℝ) * ((a)) * (-a/2 + b + c/4)^2 := by positivity
  have hid : ( (a + b + c) ^ 3 ) - ( (27 / 4) * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a)  ) = (4 : ℝ) * ((c)) * (a + b/4 - c/2)^2 + (4 : ℝ) * ((b)) * (a/4 - b/2 + c)^2 + (4 : ℝ) * ((a)) * (-a/2 + b + c/4)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a + b + c) ^ 3 ≥ (27 / 4) * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a)) := @solution
#print axioms solution
