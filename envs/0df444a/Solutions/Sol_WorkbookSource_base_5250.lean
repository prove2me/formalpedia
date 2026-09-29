-- Prove2me | solution 1 for WorkbookSource.base_5250
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:32:23.397909+00:00
-- url     : https://prove2.me/submissions/034f79e5-e8bd-4869-9d70-bf70764e9887

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 1) : a^3 + b^3 + c^3 + 6 * a * b * c ≥ 1 / 4  := by
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
  have hsum : 0 ≤ (3 : ℝ) * ((-a - b + 1)) * (a + b - 1/2)^2 + (3 : ℝ) * ((b)) * (b - 1/2)^2 + (3 : ℝ) * ((a)) * (a - 1/2)^2 := by positivity
  have hid : ( a^3 + b^3 + c^3 + 6 * a * b * c ) - ( 1 / 4  ) = (3 : ℝ) * ((-a - b + 1)) * (a + b - 1/2)^2 + (3 : ℝ) * ((b)) * (b - 1/2)^2 + (3 : ℝ) * ((a)) * (a - 1/2)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 1), a^3 + b^3 + c^3 + 6 * a * b * c ≥ 1 / 4) := @solution
#print axioms solution
