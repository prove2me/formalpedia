-- Prove2me | solution 1 for WorkbookSource.base_10651
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:32:25.303249+00:00
-- url     : https://prove2.me/submissions/4e46c7a1-3a4a-4ee3-9d23-6cafd95f087f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 7 / 9  := by
  have helim : c = (-a - b + 1) := by linarith only [habc]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 1) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (2/3 : ℝ) * (1) * (a/2 + b - 1/2)^2 + (1/2 : ℝ) * (1) * (a - 1/3)^2 + (2/3 : ℝ) * ((-a - b + 1)) * (-a + b)^2 + (8/3 : ℝ) * ((b)) * (a + b/2 - 1/2)^2 + (8/3 : ℝ) * ((a)) * (a/2 + b - 1/2)^2 := by positivity
  have hid : ( 3 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a ^ 3 + b ^ 3 + c ^ 3) ) - ( 7 / 9  ) = (2/3 : ℝ) * (1) * (a/2 + b - 1/2)^2 + (1/2 : ℝ) * (1) * (a - 1/3)^2 + (2/3 : ℝ) * ((-a - b + 1)) * (-a + b)^2 + (8/3 : ℝ) * ((b)) * (a + b/2 - 1/2)^2 + (8/3 : ℝ) * ((a)) * (a/2 + b - 1/2)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), 3 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 7 / 9) := @solution
#print axioms solution
