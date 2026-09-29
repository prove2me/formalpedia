-- Prove2me | solution 1 for WorkbookSource.base_30734
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:47:33.297025+00:00
-- url     : https://prove2.me/submissions/2c8801fd-244a-465b-adfb-fb9b52141c23

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (h : (a^2 - 2 * b)^2 + 4 * b^2 = 2 * a) :
  (a^2 - 4 * b)^2 ≤ 3  := by
  have hw0 : 0 ≤ (a^4 - 4*a^2*b - 2*a + 8*b^2) := by linarith only [h]
  have hw1 : 0 ≤ (-a^4 + 4*a^2*b + 2*a - 8*b^2) := by linarith only [h]
  have hsum : 0 ≤ (3 : ℝ) * (1) * (-a^2/3 - 2*a/3 + 1)^2 + (2/3 : ℝ) * (1) * (-a^2 + a)^2 + (2 : ℝ) * ((-a^4 + 4*a^2*b + 2*a - 8*b^2)) * (1)^2 := by positivity
  have hid : ( 3  ) - (
  (a^2 - 4 * b)^2 ) = (3 : ℝ) * (1) * (-a^2/3 - 2*a/3 + 1)^2 + (2/3 : ℝ) * (1) * (-a^2 + a)^2 + (2 : ℝ) * ((-a^4 + 4*a^2*b + 2*a - 8*b^2)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (h : (a^2 - 2 * b)^2 + 4 * b^2 = 2 * a), (a^2 - 4 * b)^2 ≤ 3) := @solution
#print axioms solution
