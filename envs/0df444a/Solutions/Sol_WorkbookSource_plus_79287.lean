-- Prove2me | solution 1 for WorkbookSource.plus_79287
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:45.359781+00:00
-- url     : https://prove2.me/submissions/eb84bfcc-9363-4c33-ab29-d88797cb4b7c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a^2 + 2 * b = 1) (hb : b^2 + 4 * c = -1) : 89 / 256 ≤ a^2 + b^2 + c^2   := by
  have hw0 : 0 ≤ (a^2 + 2*b - 1) := by linarith only [ha]
  have hw1 : 0 ≤ (-a^2 - 2*b + 1) := by linarith only [ha]
  have hw2 : 0 ≤ (b^2 + 4*c + 1) := by linarith only [hb]
  have hw3 : 0 ≤ (-b^2 - 4*c - 1) := by linarith only [hb]
  have hsum : 0 ≤ (37/32 : ℝ) * (1) * (b - 1/2)^2 + (1 : ℝ) * (1) * (c + 5/16)^2 + (27/64 : ℝ) * (1) * (a)^2 + (5/32 : ℝ) * ((-b^2 - 4*c - 1)) * (1)^2 + (37/64 : ℝ) * ((a^2 + 2*b - 1)) * (1)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2   ) - ( 89 / 256 ) = (37/32 : ℝ) * (1) * (b - 1/2)^2 + (1 : ℝ) * (1) * (c + 5/16)^2 + (27/64 : ℝ) * (1) * (a)^2 + (5/32 : ℝ) * ((-b^2 - 4*c - 1)) * (1)^2 + (37/64 : ℝ) * ((a^2 + 2*b - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a^2 + 2 * b = 1) (hb : b^2 + 4 * c = -1), 89 / 256 ≤ a^2 + b^2 + c^2) := @solution
#print axioms solution
