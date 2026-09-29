-- Prove2me | solution 1 for WorkbookSource.plus_4889
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:32:33.990187+00:00
-- url     : https://prove2.me/submissions/42e583fe-2bce-48d8-9e6c-9e5972443a44

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a * d - b * c) ^ 2 ≤ (a + b) * (c + d) * ((a - c) ^ 2 + (b - d) ^ 2)   := by
  have hsum : 0 ≤ (1 : ℝ) * (b*d) * (-b + d)^2 + (1 : ℝ) * (b*c) * (-a/2 - b + c/2 + d)^2 + (3/4 : ℝ) * (b*c) * (-a + c)^2 + (1 : ℝ) * (a*d) * (-a/2 - b + c/2 + d)^2 + (3/4 : ℝ) * (a*d) * (-a + c)^2 + (1 : ℝ) * (a*c) * (-a + c)^2 := by positivity
  have hid : ( (a + b) * (c + d) * ((a - c) ^ 2 + (b - d) ^ 2)   ) - ( (a * d - b * c) ^ 2 ) = (1 : ℝ) * (b*d) * (-b + d)^2 + (1 : ℝ) * (b*c) * (-a/2 - b + c/2 + d)^2 + (3/4 : ℝ) * (b*c) * (-a + c)^2 + (1 : ℝ) * (a*d) * (-a/2 - b + c/2 + d)^2 + (3/4 : ℝ) * (a*d) * (-a + c)^2 + (1 : ℝ) * (a*c) * (-a + c)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d), (a * d - b * c) ^ 2 ≤ (a + b) * (c + d) * ((a - c) ^ 2 + (b - d) ^ 2)) := @solution
#print axioms solution
