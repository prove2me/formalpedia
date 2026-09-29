-- Prove2me | solution 1 for WorkbookSource.base_31826
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:33:48.477563+00:00
-- url     : https://prove2.me/submissions/fa878eec-08d0-486f-ae59-ef263c3b6a50

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : (2 + c + c^3) / 4 ≥ a * b * c + a * b + 2 * b * c + 2 * c * a  := by
  have helim : c = (-a - b + 1) := by linarith only [hab]
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
  have hsum : 0 ≤ (5/2 : ℝ) * (1) * (4*a/5 + b - 3/5)^2 + (9/10 : ℝ) * (1) * (a - 1/3)^2 + (1/4 : ℝ) * ((-a - b + 1)) * (-a + b)^2 := by positivity
  have hid : ( (2 + c + c^3) / 4 ) - ( a * b * c + a * b + 2 * b * c + 2 * c * a  ) = (5/2 : ℝ) * (1) * (4*a/5 + b - 3/5)^2 + (9/10 : ℝ) * (1) * (a - 1/3)^2 + (1/4 : ℝ) * ((-a - b + 1)) * (-a + b)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1), (2 + c + c^3) / 4 ≥ a * b * c + a * b + 2 * b * c + 2 * c * a) := @solution
#print axioms solution
