-- Prove2me | solution 1 for WorkbookSource.base_38972
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:52:12.327873+00:00
-- url     : https://prove2.me/submissions/755ea9e7-3cec-4fe9-a41f-2650623dc9a5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x + y = 3) : 9 * (x - 1) * (y - 1) + (y^2 + y + 1) * (x + 1) + (x^2 - x + 1) * (y - 1) ≥ 9  := by
  have helim : y = (3 - x) := by linarith only [hxy]
  have hw0 : 0 ≤ (x - 1) := by
    have hh := hx
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (2 - x) := by
    have hh := hy
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (6 : ℝ) * ((2 - x)) * (1)^2 + (12 : ℝ) * ((x - 1) * (2 - x)) * (1)^2 := by positivity
  have hid : ( 9 * (x - 1) * (y - 1) + (y^2 + y + 1) * (x + 1) + (x^2 - x + 1) * (y - 1) ) - ( 9  ) = (6 : ℝ) * ((2 - x)) * (1)^2 + (12 : ℝ) * ((x - 1) * (2 - x)) * (1)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x + y = 3), 9 * (x - 1) * (y - 1) + (y^2 + y + 1) * (x + 1) + (x^2 - x + 1) * (y - 1) ≥ 9) := @solution
#print axioms solution
