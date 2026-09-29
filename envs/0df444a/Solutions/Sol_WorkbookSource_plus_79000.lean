-- Prove2me | solution 1 for WorkbookSource.plus_79000
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:20:12.697979+00:00
-- url     : https://prove2.me/submissions/e28361c5-3932-4a68-a01c-c5699171031e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) : (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d) - 27 / 4 * (c * d + a * b) * (b * c + a * d) - 27 / 4 * (a * c + b * d) * (b * c + a * d) - 27 / 4 * (c * d + a * b) * (a * c + b * d) ≥ 0   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (d) := by linarith only [hd]
  have hsum : 0 ≤ (1/3 : ℝ) * (1) * (-a*b + c*d)^2 + (1/3 : ℝ) * (1) * (-a*c + b*d)^2 + (1/3 : ℝ) * (1) * (-a*d + b*c)^2 + (1 : ℝ) * ((c) * (d)) * (-11*a/12 - 11*b/12 + 5*c/6 + d)^2 + (11/36 : ℝ) * ((c) * (d)) * (-a/2 - b/2 + c)^2 + (1 : ℝ) * ((b) * (d)) * (-11*a/12 + 5*b/6 - 11*c/12 + d)^2 + (11/36 : ℝ) * ((b) * (d)) * (-a/2 + b - c/2)^2 + (1 : ℝ) * ((b) * (c)) * (-11*a/12 + 5*b/6 + c - 11*d/12)^2 + (11/36 : ℝ) * ((b) * (c)) * (-a/2 + b - d/2)^2 + (1 : ℝ) * ((a) * (d)) * (5*a/6 - 11*b/12 - 11*c/12 + d)^2 + (11/36 : ℝ) * ((a) * (d)) * (a - b/2 - c/2)^2 + (1 : ℝ) * ((a) * (c)) * (5*a/6 - 11*b/12 + c - 11*d/12)^2 + (11/36 : ℝ) * ((a) * (c)) * (a - b/2 - d/2)^2 + (1 : ℝ) * ((a) * (b)) * (5*a/6 + b - 11*c/12 - 11*d/12)^2 + (11/36 : ℝ) * ((a) * (b)) * (a - c/2 - d/2)^2 := by positivity
  have hid : ( (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d) - 27 / 4 * (c * d + a * b) * (b * c + a * d) - 27 / 4 * (a * c + b * d) * (b * c + a * d) - 27 / 4 * (c * d + a * b) * (a * c + b * d) ) - ( 0   ) = (1/3 : ℝ) * (1) * (-a*b + c*d)^2 + (1/3 : ℝ) * (1) * (-a*c + b*d)^2 + (1/3 : ℝ) * (1) * (-a*d + b*c)^2 + (1 : ℝ) * ((c) * (d)) * (-11*a/12 - 11*b/12 + 5*c/6 + d)^2 + (11/36 : ℝ) * ((c) * (d)) * (-a/2 - b/2 + c)^2 + (1 : ℝ) * ((b) * (d)) * (-11*a/12 + 5*b/6 - 11*c/12 + d)^2 + (11/36 : ℝ) * ((b) * (d)) * (-a/2 + b - c/2)^2 + (1 : ℝ) * ((b) * (c)) * (-11*a/12 + 5*b/6 + c - 11*d/12)^2 + (11/36 : ℝ) * ((b) * (c)) * (-a/2 + b - d/2)^2 + (1 : ℝ) * ((a) * (d)) * (5*a/6 - 11*b/12 - 11*c/12 + d)^2 + (11/36 : ℝ) * ((a) * (d)) * (a - b/2 - c/2)^2 + (1 : ℝ) * ((a) * (c)) * (5*a/6 - 11*b/12 + c - 11*d/12)^2 + (11/36 : ℝ) * ((a) * (c)) * (a - b/2 - d/2)^2 + (1 : ℝ) * ((a) * (b)) * (5*a/6 + b - 11*c/12 - 11*d/12)^2 + (11/36 : ℝ) * ((a) * (b)) * (a - c/2 - d/2)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0), (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d) - 27 / 4 * (c * d + a * b) * (b * c + a * d) - 27 / 4 * (a * c + b * d) * (b * c + a * d) - 27 / 4 * (c * d + a * b) * (a * c + b * d) ≥ 0) := @solution
#print axioms solution
