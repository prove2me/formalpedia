-- Prove2me | solution 1 for WorkbookSource.base_6148
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:32:23.99897+00:00
-- url     : https://prove2.me/submissions/9879a96c-1402-4d75-9aa8-2069ccb94522

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 2) : b^2 * c^2 + c^2 * a^2 + a^2 * b^2 + (11 / 8) * a * b * c ≤ 1  := by
  have helim : c = (-a - b + 2) := by linarith only [hab]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 2) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (7/4 : ℝ) * (1) * (-a^2/14 - 5*a*b/7 + 11*a/14 - 2*b^2/7 + b - 5/7)^2 + (75/112 : ℝ) * (1) * (-3*a^2/5 - 2*a*b/5 + a + 2*b^2/5 - 2/5)^2 + (5/4 : ℝ) * ((b) * (-a - b + 2)) * (-a/2 - b + 1)^2 + (5/4 : ℝ) * ((a) * (-a - b + 2)) * (-a - b/2 + 1)^2 + (5/16 : ℝ) * ((a) * (b)) * (-a + b)^2 := by positivity
  have hid : ( 1  ) - ( b^2 * c^2 + c^2 * a^2 + a^2 * b^2 + (11 / 8) * a * b * c ) = (7/4 : ℝ) * (1) * (-a^2/14 - 5*a*b/7 + 11*a/14 - 2*b^2/7 + b - 5/7)^2 + (75/112 : ℝ) * (1) * (-3*a^2/5 - 2*a*b/5 + a + 2*b^2/5 - 2/5)^2 + (5/4 : ℝ) * ((b) * (-a - b + 2)) * (-a/2 - b + 1)^2 + (5/4 : ℝ) * ((a) * (-a - b + 2)) * (-a - b/2 + 1)^2 + (5/16 : ℝ) * ((a) * (b)) * (-a + b)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 2), b^2 * c^2 + c^2 * a^2 + a^2 * b^2 + (11 / 8) * a * b * c ≤ 1) := @solution
#print axioms solution
