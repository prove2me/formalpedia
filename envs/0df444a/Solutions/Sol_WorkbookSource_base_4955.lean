-- Prove2me | solution 1 for WorkbookSource.base_4955
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:52:07.596433+00:00
-- url     : https://prove2.me/submissions/b8b01eb7-63e0-476e-938f-f863e64dd25e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : (1 - a) * (2 - b) * (2 - c) ≥ 48 * a * b * c  := by
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
  have hsum : 0 ≤ (7 : ℝ) * (1) * (a/2 + b - 1/2)^2 + (25/4 : ℝ) * ((-a - b + 1)) * (a - 4*b/5 - 1/5)^2 + (81/4 : ℝ) * ((b)) * (a + 4*b/9 - 5/9)^2 + (25 : ℝ) * ((a)) * (a/2 + b - 1/2)^2 := by positivity
  have hid : ( (1 - a) * (2 - b) * (2 - c) ) - ( 48 * a * b * c  ) = (7 : ℝ) * (1) * (a/2 + b - 1/2)^2 + (25/4 : ℝ) * ((-a - b + 1)) * (a - 4*b/5 - 1/5)^2 + (81/4 : ℝ) * ((b)) * (a + 4*b/9 - 5/9)^2 + (25 : ℝ) * ((a)) * (a/2 + b - 1/2)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), (1 - a) * (2 - b) * (2 - c) ≥ 48 * a * b * c) := @solution
#print axioms solution
