-- Prove2me | solution 1 for WorkbookSource.plus_70452
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:04:42.879342+00:00
-- url     : https://prove2.me/submissions/12c8c852-d81d-4de3-a280-5b1c594bffcb

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h1 : (a ^ 2 - a * b + b ^ 2) ^ 2 + (b ^ 2 - b * c + c ^ 2) ^ 2 + (c ^ 2 - c * a + a ^ 2) ^ 2 = 3) : (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 + 12 ≥ 8 * (a ^ 3 + b ^ 3 + c ^ 3)   := by
  have hw0 : 0 ≤ (2*a^4 - 2*a^3*b - 2*a^3*c + 3*a^2*b^2 + 3*a^2*c^2 - 2*a*b^3 - 2*a*c^3 + 2*b^4 - 2*b^3*c + 3*b^2*c^2 - 2*b*c^3 + 2*c^4 - 3) := by linarith only [h1]
  have hw1 : 0 ≤ (-2*a^4 + 2*a^3*b + 2*a^3*c - 3*a^2*b^2 - 3*a^2*c^2 + 2*a*b^3 + 2*a*c^3 - 2*b^4 + 2*b^3*c - 3*b^2*c^2 + 2*b*c^3 - 2*c^4 + 3) := by linarith only [h1]
  have hsum : 0 ≤ (8 : ℝ) * (1) * (a^2/2 - a*c/2 - a/4 + b^2/2 - b*c/2 - b/4 + c^2 - c/2)^2 + (6 : ℝ) * (1) * (a^2/3 - 2*a*b/3 + a*c/3 - a/6 + b^2 - b*c/3 - b/2)^2 + (16/3 : ℝ) * (1) * (a^2 - a*b/2 - a*c/2 - a/2 + b*c/2)^2 + (4 : ℝ) * ((-2*a^4 + 2*a^3*b + 2*a^3*c - 3*a^2*b^2 - 3*a^2*c^2 + 2*a*b^3 + 2*a*c^3 - 2*b^4 + 2*b^3*c - 3*b^2*c^2 + 2*b*c^3 - 2*c^4 + 3)) * (1)^2 := by positivity
  have hid : ( (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 + 12 ) - ( 8 * (a ^ 3 + b ^ 3 + c ^ 3)   ) = (8 : ℝ) * (1) * (a^2/2 - a*c/2 - a/4 + b^2/2 - b*c/2 - b/4 + c^2 - c/2)^2 + (6 : ℝ) * (1) * (a^2/3 - 2*a*b/3 + a*c/3 - a/6 + b^2 - b*c/3 - b/2)^2 + (16/3 : ℝ) * (1) * (a^2 - a*b/2 - a*c/2 - a/2 + b*c/2)^2 + (4 : ℝ) * ((-2*a^4 + 2*a^3*b + 2*a^3*c - 3*a^2*b^2 - 3*a^2*c^2 + 2*a*b^3 + 2*a*c^3 - 2*b^4 + 2*b^3*c - 3*b^2*c^2 + 2*b*c^3 - 2*c^4 + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h1 : (a ^ 2 - a * b + b ^ 2) ^ 2 + (b ^ 2 - b * c + c ^ 2) ^ 2 + (c ^ 2 - c * a + a ^ 2) ^ 2 = 3), (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 + 12 ≥ 8 * (a ^ 3 + b ^ 3 + c ^ 3)) := @solution
#print axioms solution
