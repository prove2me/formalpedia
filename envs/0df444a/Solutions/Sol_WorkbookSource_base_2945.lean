-- Prove2me | solution 1 for WorkbookSource.base_2945
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:52:06.878015+00:00
-- url     : https://prove2.me/submissions/b17e74b4-ab9b-439a-a8a3-941b73e77dc5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 2 * a - b = 2) : a ^ 4 + (a - b) ^ 4 + a ^ 2 * b ≥ a ^ 3 + (a - b) ^ 3 + a * b ^ 2  := by
  have helim : b = (2*a - 2) := by linarith only [hab]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (2*a - 2) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (8 : ℝ) * (1) * (1 - a)^2 + (4 : ℝ) * ((a) * (2*a - 2)) * (1 - a/2)^2 := by positivity
  have hid : ( a ^ 4 + (a - b) ^ 4 + a ^ 2 * b ) - ( a ^ 3 + (a - b) ^ 3 + a * b ^ 2  ) = (8 : ℝ) * (1) * (1 - a)^2 + (4 : ℝ) * ((a) * (2*a - 2)) * (1 - a/2)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 2 * a - b = 2), a ^ 4 + (a - b) ^ 4 + a ^ 2 * b ≥ a ^ 3 + (a - b) ^ 3 + a * b ^ 2) := @solution
#print axioms solution
