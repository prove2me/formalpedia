-- Prove2me | solution 1 for WorkbookSource.base_39574
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:32:07.930975+00:00
-- url     : https://prove2.me/submissions/2d9115f0-4c83-4d97-993b-c9819de45987

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution  (a b c d : ℝ)
  (h₀ : 0 ≤ a)
  (h₁ : 0 ≤ b)
  (h₂ : 0 ≤ c)
  (h₃ : 0 ≤ d) :
  (a^2 + b^2 + c^2 + d^2)^2 ≥ 4 * (a - b) * (b - c) * (c - d) * (d - a) + 16 * a * b * c * d  := by
  have hsum : 0 ≤ (26/9 : ℝ) * (1) * (a^2/13 - 11*a*b/13 - a*d/13 + b^2/13 - b*c/13 - c^2/13 + c*d - d^2/13)^2 + (112/39 : ℝ) * (1) * (a^2/12 - a*b/7 - 6*a*d/7 - b^2/14 + b*c - c^2/12 + d^2/14)^2 + (61/63 : ℝ) * (1) * (4*a*b/61 - 4*a*d/61 - b^2 + d^2)^2 + (26/27 : ℝ) * (1) * (-a^2 + c^2)^2 + (416/549 : ℝ) * (1) * (-a*b + a*d)^2 + (16/9 : ℝ) * (c*d) * (-a + b - c/2 + d/2)^2 + (16/9 : ℝ) * (b*c) * (-a + b/2 - c/2 + d)^2 + (16/9 : ℝ) * (a*d) * (a/2 - b + c - d/2)^2 + (16/9 : ℝ) * (a*b) * (-a/2 + b/2 - c + d)^2 := by positivity
  have hid : (
  (a^2 + b^2 + c^2 + d^2)^2 ) - ( 4 * (a - b) * (b - c) * (c - d) * (d - a) + 16 * a * b * c * d  ) = (26/9 : ℝ) * (1) * (a^2/13 - 11*a*b/13 - a*d/13 + b^2/13 - b*c/13 - c^2/13 + c*d - d^2/13)^2 + (112/39 : ℝ) * (1) * (a^2/12 - a*b/7 - 6*a*d/7 - b^2/14 + b*c - c^2/12 + d^2/14)^2 + (61/63 : ℝ) * (1) * (4*a*b/61 - 4*a*d/61 - b^2 + d^2)^2 + (26/27 : ℝ) * (1) * (-a^2 + c^2)^2 + (416/549 : ℝ) * (1) * (-a*b + a*d)^2 + (16/9 : ℝ) * (c*d) * (-a + b - c/2 + d/2)^2 + (16/9 : ℝ) * (b*c) * (-a + b/2 - c/2 + d)^2 + (16/9 : ℝ) * (a*d) * (a/2 - b + c - d/2)^2 + (16/9 : ℝ) * (a*b) * (-a/2 + b/2 - c + d)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ)
  (h₀ : 0 ≤ a)
  (h₁ : 0 ≤ b)
  (h₂ : 0 ≤ c)
  (h₃ : 0 ≤ d), (a^2 + b^2 + c^2 + d^2)^2 ≥ 4 * (a - b) * (b - c) * (c - d) * (d - a) + 16 * a * b * c * d) := @solution
#print axioms solution
