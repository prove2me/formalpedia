-- Prove2me | solution 1 for WorkbookSource.base_27309
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:52:10.403094+00:00
-- url     : https://prove2.me/submissions/4ebfaffe-af06-4ca3-a063-da1bcffef1d2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) (h : a * b * c ≥ -4) : 3 * (a * b * c + 4) ≥ 5 * (a * b + b * c + c * a)  := by
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
  have hw3 : 0 ≤ (-a^2*b - a*b^2 + 3*a*b + 4) := by
    have hh := h
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (4 : ℝ) * ((-a - b + 3)) * (-a/2 - b/2 + 1)^2 + (1 : ℝ) * ((b)) * (1 - b)^2 + (1 : ℝ) * ((a)) * (1 - a)^2 := by positivity
  have hid : ( 3 * (a * b * c + 4) ) - ( 5 * (a * b + b * c + c * a)  ) = (4 : ℝ) * ((-a - b + 3)) * (-a/2 - b/2 + 1)^2 + (1 : ℝ) * ((b)) * (1 - b)^2 + (1 : ℝ) * ((a)) * (1 - a)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) (h : a * b * c ≥ -4), 3 * (a * b * c + 4) ≥ 5 * (a * b + b * c + c * a)) := @solution
#print axioms solution
