-- Prove2me | solution 1 for WorkbookSource.plus_51825
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:40:07.992223+00:00
-- url     : https://prove2.me/submissions/1a5cc715-baab-4df3-9be8-e6f45306272d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c: ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a^2 + a * b + b^2 ≤ 18) (hbc : b^2 + b * c + c^2 ≤ 6) : a * b + b * c + c * a ≤ 12   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (-a^2 - a*b - b^2 + 18) := by linarith only [hab]
  have hw4 : 0 ≤ (-b^2 - b*c - c^2 + 6) := by linarith only [hbc]
  have hsum : 0 ≤ (4/3 : ℝ) * (1) * (-a/4 + b)^2 + (1 : ℝ) * (1) * (-a/2 + c)^2 + (1 : ℝ) * ((-b^2 - b*c - c^2 + 6)) * (1)^2 + (1/3 : ℝ) * ((-a^2 - a*b - b^2 + 18)) * (1)^2 := by positivity
  have hid : ( 12   ) - ( a * b + b * c + c * a ) = (4/3 : ℝ) * (1) * (-a/4 + b)^2 + (1 : ℝ) * (1) * (-a/2 + c)^2 + (1 : ℝ) * ((-b^2 - b*c - c^2 + 6)) * (1)^2 + (1/3 : ℝ) * ((-a^2 - a*b - b^2 + 18)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c: ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a^2 + a * b + b^2 ≤ 18) (hbc : b^2 + b * c + c^2 ≤ 6), a * b + b * c + c * a ≤ 12) := @solution
#print axioms solution
