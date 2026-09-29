-- Prove2me | solution 1 for WorkbookSource.base_16964
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:56:11.329973+00:00
-- url     : https://prove2.me/submissions/72554e48-b0b2-456c-997d-ddf5ba1fa262

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 9) : a * b * c + 5 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 162  := by
  have helim : c = (-a - b + 9) := by linarith only [habc]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 9) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (27 : ℝ) * ((-a - b + 9)) * (-a/6 - b/6 + 1)^2 + (1/12 : ℝ) * ((-a - b + 9)) * (-a + b)^2 + (18 : ℝ) * ((b)) * (-11*a/72 - 13*b/72 + 1)^2 + (71/288 : ℝ) * ((b)) * (-a + b)^2 + (18 : ℝ) * ((a)) * (-13*a/72 - 11*b/72 + 1)^2 + (71/288 : ℝ) * ((a)) * (-a + b)^2 := by positivity
  have hid : ( a * b * c + 5 * (a ^ 2 + b ^ 2 + c ^ 2) ) - ( 162  ) = (27 : ℝ) * ((-a - b + 9)) * (-a/6 - b/6 + 1)^2 + (1/12 : ℝ) * ((-a - b + 9)) * (-a + b)^2 + (18 : ℝ) * ((b)) * (-11*a/72 - 13*b/72 + 1)^2 + (71/288 : ℝ) * ((b)) * (-a + b)^2 + (18 : ℝ) * ((a)) * (-13*a/72 - 11*b/72 + 1)^2 + (71/288 : ℝ) * ((a)) * (-a + b)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 9), a * b * c + 5 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 162) := @solution
#print axioms solution
