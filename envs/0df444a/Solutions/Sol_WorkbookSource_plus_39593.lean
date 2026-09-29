-- Prove2me | solution 1 for WorkbookSource.plus_39593
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:33:52.506586+00:00
-- url     : https://prove2.me/submissions/3c84fa41-2860-4328-a2e6-87a3fdb50131

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c: ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) : a * b + c * a + 13 / 3 ≥ b * c   := by
  have helim : c = (-a - b + 3) := by linarith only [habc]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 3) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (4/3 : ℝ) * (1) * (-3*a/40 - 3*b/4 + 1)^2 + (157/400 : ℝ) * (1) * (a + 110*b/157)^2 + (9/157 : ℝ) * (1) * (b)^2 + (1 : ℝ) * ((-a - b + 3)) * (1)^2 + (7/5 : ℝ) * ((a) * (-a - b + 3)) * (1)^2 + (17/10 : ℝ) * ((a) * (b)) * (1)^2 := by positivity
  have hid : ( a * b + c * a + 13 / 3 ) - ( b * c   ) = (4/3 : ℝ) * (1) * (-3*a/40 - 3*b/4 + 1)^2 + (157/400 : ℝ) * (1) * (a + 110*b/157)^2 + (9/157 : ℝ) * (1) * (b)^2 + (1 : ℝ) * ((-a - b + 3)) * (1)^2 + (7/5 : ℝ) * ((a) * (-a - b + 3)) * (1)^2 + (17/10 : ℝ) * ((a) * (b)) * (1)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c: ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3), a * b + c * a + 13 / 3 ≥ b * c) := @solution
#print axioms solution
