-- Prove2me | solution 1 for WorkbookSource.plus_39693
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:20:08.24241+00:00
-- url     : https://prove2.me/submissions/0919c1db-e65f-47b1-9981-0d8666be75cd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d) - (27 / 32) * (a + b + c + d) ^ 2 * (a * c + b * d) - (27 / 32) * (a + b + c + d) ^ 2 * (c * d + a * b) - (27 / 32) * (a + b + c + d) ^ 2 * (b * c + a * d) ≥ 0   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (d) := by linarith only [hd]
  have hsum : 0 ≤ (1/3 : ℝ) * (1) * (-a*b + c*d)^2 + (1/3 : ℝ) * (1) * (-a*c + b*d)^2 + (1/3 : ℝ) * (1) * (-a*d + b*c)^2 + (5/32 : ℝ) * ((c) * (d)) * (-7*a/15 - 7*b/15 - c/15 + d)^2 + (7/45 : ℝ) * ((c) * (d)) * (-a/2 - b/2 + c)^2 + (5/32 : ℝ) * ((b) * (d)) * (-7*a/15 - b/15 - 7*c/15 + d)^2 + (7/45 : ℝ) * ((b) * (d)) * (-a/2 + b - c/2)^2 + (5/32 : ℝ) * ((b) * (c)) * (-7*a/15 - b/15 + c - 7*d/15)^2 + (7/45 : ℝ) * ((b) * (c)) * (-a/2 + b - d/2)^2 + (5/32 : ℝ) * ((a) * (d)) * (-a/15 - 7*b/15 - 7*c/15 + d)^2 + (7/45 : ℝ) * ((a) * (d)) * (a - b/2 - c/2)^2 + (5/32 : ℝ) * ((a) * (c)) * (-a/15 - 7*b/15 + c - 7*d/15)^2 + (7/45 : ℝ) * ((a) * (c)) * (a - b/2 - d/2)^2 + (5/32 : ℝ) * ((a) * (b)) * (-a/15 + b - 7*c/15 - 7*d/15)^2 + (7/45 : ℝ) * ((a) * (b)) * (a - c/2 - d/2)^2 := by positivity
  have hid : ( (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d) - (27 / 32) * (a + b + c + d) ^ 2 * (a * c + b * d) - (27 / 32) * (a + b + c + d) ^ 2 * (c * d + a * b) - (27 / 32) * (a + b + c + d) ^ 2 * (b * c + a * d) ) - ( 0   ) = (1/3 : ℝ) * (1) * (-a*b + c*d)^2 + (1/3 : ℝ) * (1) * (-a*c + b*d)^2 + (1/3 : ℝ) * (1) * (-a*d + b*c)^2 + (5/32 : ℝ) * ((c) * (d)) * (-7*a/15 - 7*b/15 - c/15 + d)^2 + (7/45 : ℝ) * ((c) * (d)) * (-a/2 - b/2 + c)^2 + (5/32 : ℝ) * ((b) * (d)) * (-7*a/15 - b/15 - 7*c/15 + d)^2 + (7/45 : ℝ) * ((b) * (d)) * (-a/2 + b - c/2)^2 + (5/32 : ℝ) * ((b) * (c)) * (-7*a/15 - b/15 + c - 7*d/15)^2 + (7/45 : ℝ) * ((b) * (c)) * (-a/2 + b - d/2)^2 + (5/32 : ℝ) * ((a) * (d)) * (-a/15 - 7*b/15 - 7*c/15 + d)^2 + (7/45 : ℝ) * ((a) * (d)) * (a - b/2 - c/2)^2 + (5/32 : ℝ) * ((a) * (c)) * (-a/15 - 7*b/15 + c - 7*d/15)^2 + (7/45 : ℝ) * ((a) * (c)) * (a - b/2 - d/2)^2 + (5/32 : ℝ) * ((a) * (b)) * (-a/15 + b - 7*c/15 - 7*d/15)^2 + (7/45 : ℝ) * ((a) * (b)) * (a - c/2 - d/2)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d), (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d) - (27 / 32) * (a + b + c + d) ^ 2 * (a * c + b * d) - (27 / 32) * (a + b + c + d) ^ 2 * (c * d + a * b) - (27 / 32) * (a + b + c + d) ^ 2 * (b * c + a * d) ≥ 0) := @solution
#print axioms solution
