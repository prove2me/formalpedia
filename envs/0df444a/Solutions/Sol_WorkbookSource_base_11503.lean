-- Prove2me | solution 1 for WorkbookSource.base_11503
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:32:25.957662+00:00
-- url     : https://prove2.me/submissions/e3b6920e-69c4-4495-aca3-0b3df86d5bfa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a^2 + 2 * b = c) (hbc : b^2 + 2 * c = a) : a + b + c ≤ 3 / 4  := by
  have helim : c = (a^2 + 2*b) := by linarith only [hab]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (a^2 + 2*b) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hw3 : 0 ≤ (2*a^2 - a + b^2 + 4*b) := by
    have hh := hbc
    try simp only [helim] at hh
    linarith only [hh]
  have hw4 : 0 ≤ (-2*a^2 + a - b^2 - 4*b) := by
    have hh := hbc
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (3 : ℝ) * (1) * (a - 1/2)^2 + (2 : ℝ) * (1) * (b)^2 + (2 : ℝ) * ((-2*a^2 + a - b^2 - 4*b)) * (1)^2 + (5 : ℝ) * ((b)) * (1)^2 := by positivity
  have hid : ( 3 / 4  ) - ( a + b + c ) = (3 : ℝ) * (1) * (a - 1/2)^2 + (2 : ℝ) * (1) * (b)^2 + (2 : ℝ) * ((-2*a^2 + a - b^2 - 4*b)) * (1)^2 + (5 : ℝ) * ((b)) * (1)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a^2 + 2 * b = c) (hbc : b^2 + 2 * c = a), a + b + c ≤ 3 / 4) := @solution
#print axioms solution
