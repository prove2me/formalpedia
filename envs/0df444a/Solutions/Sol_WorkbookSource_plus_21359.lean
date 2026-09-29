-- Prove2me | solution 1 for WorkbookSource.plus_21359
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:33:51.796007+00:00
-- url     : https://prove2.me/submissions/4ef791e7-6255-4a8c-abbf-f7bf4ae00108

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : a * b * (1 - c) + b * c * (1 - a) + c * a * (1 - b) ≤ 9 / 4   := by
  have helim : c = (-a - b + 3) := by linarith only [hab]
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
  have hsum : 0 ≤ (3/4 : ℝ) * ((-a - b + 3)) * (-2*a/3 - 2*b/3 + 1)^2 + (3/4 : ℝ) * ((b)) * (1 - 2*b/3)^2 + (3/4 : ℝ) * ((a)) * (1 - 2*a/3)^2 + (2 : ℝ) * ((a) * (b) * (-a - b + 3)) * (1)^2 := by positivity
  have hid : ( 9 / 4   ) - ( a * b * (1 - c) + b * c * (1 - a) + c * a * (1 - b) ) = (3/4 : ℝ) * ((-a - b + 3)) * (-2*a/3 - 2*b/3 + 1)^2 + (3/4 : ℝ) * ((b)) * (1 - 2*b/3)^2 + (3/4 : ℝ) * ((a)) * (1 - 2*a/3)^2 + (2 : ℝ) * ((a) * (b) * (-a - b + 3)) * (1)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), a * b * (1 - c) + b * c * (1 - a) + c * a * (1 - b) ≤ 9 / 4) := @solution
#print axioms solution
