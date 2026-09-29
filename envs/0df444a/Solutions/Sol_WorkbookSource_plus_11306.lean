-- Prove2me | solution 1 for WorkbookSource.plus_11306
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:33:51.111776+00:00
-- url     : https://prove2.me/submissions/80ac0360-0575-426e-b00d-d4c69a0f3ac6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) + 16 / 9 ≥ 6 * (a * b + b * c + c * a)   := by
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
  have hsum : 0 ≤ (16/3 : ℝ) * (1) * (a/2 + b - 1/2)^2 + (4 : ℝ) * (1) * (a - 1/3)^2 + (1/3 : ℝ) * ((-a - b + 1)) * (-a + b)^2 + (4/3 : ℝ) * ((b)) * (a + b/2 - 1/2)^2 + (4/3 : ℝ) * ((a)) * (a/2 + b - 1/2)^2 := by positivity
  have hid : ( a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) + 16 / 9 ) - ( 6 * (a * b + b * c + c * a)   ) = (16/3 : ℝ) * (1) * (a/2 + b - 1/2)^2 + (4 : ℝ) * (1) * (a - 1/3)^2 + (1/3 : ℝ) * ((-a - b + 1)) * (-a + b)^2 + (4/3 : ℝ) * ((b)) * (a + b/2 - 1/2)^2 + (4/3 : ℝ) * ((a)) * (a/2 + b - 1/2)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) + 16 / 9 ≥ 6 * (a * b + b * c + c * a)) := @solution
#print axioms solution
