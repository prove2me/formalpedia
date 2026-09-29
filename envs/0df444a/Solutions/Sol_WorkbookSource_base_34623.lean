-- Prove2me | solution 1 for WorkbookSource.base_34623
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:52:11.739896+00:00
-- url     : https://prove2.me/submissions/073752cb-84f6-43ae-80ce-4de24c57929c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h1 : x + y + z = 1) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^4 + y^4 + z^4 + 1 ≥ 2 * (x^2 + y^2 + z^2)  := by
  have helim : z = (-x - y + 1) := by linarith only [h1]
  have hw0 : 0 ≤ (x) := by
    have hh := hx
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (y) := by
    have hh := hy
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-x - y + 1) := by
    have hh := hz
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-x^2 - x*y + x - y^2 + y)^2 + (4 : ℝ) * ((x) * (y) * (-x - y + 1)) * (1)^2 := by positivity
  have hid : ( x^4 + y^4 + z^4 + 1 ) - ( 2 * (x^2 + y^2 + z^2)  ) = (2 : ℝ) * (1) * (-x^2 - x*y + x - y^2 + y)^2 + (4 : ℝ) * ((x) * (y) * (-x - y + 1)) * (1)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h1 : x + y + z = 1) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x^4 + y^4 + z^4 + 1 ≥ 2 * (x^2 + y^2 + z^2)) := @solution
#print axioms solution
