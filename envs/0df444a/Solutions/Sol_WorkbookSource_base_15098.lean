-- Prove2me | solution 1 for WorkbookSource.base_15098
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:32:27.241511+00:00
-- url     : https://prove2.me/submissions/25b029a6-ec9e-4b2b-9b84-585918731ba8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 + b^2 + c^2 + 3 * a * b * c ≥ 4 / 9  := by
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
  have hsum : 0 ≤ (13/32 : ℝ) * (1) * (a + b - 2/3)^2 + (27/32 : ℝ) * ((-a - b + 1)) * (a + b - 2/3)^2 + (27/32 : ℝ) * ((b)) * (-a/3 + b - 2/9)^2 + (27/32 : ℝ) * ((a)) * (a - b/3 - 2/9)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2 + 3 * a * b * c ) - ( 4 / 9  ) = (13/32 : ℝ) * (1) * (a + b - 2/3)^2 + (27/32 : ℝ) * ((-a - b + 1)) * (a + b - 2/3)^2 + (27/32 : ℝ) * ((b)) * (-a/3 + b - 2/9)^2 + (27/32 : ℝ) * ((a)) * (a - b/3 - 2/9)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), a^2 + b^2 + c^2 + 3 * a * b * c ≥ 4 / 9) := @solution
#print axioms solution
