-- Prove2me | solution 1 for WorkbookSource.plus_4648
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:06:47.456492+00:00
-- url     : https://prove2.me/submissions/8b3d6650-0663-4a40-aa5a-69193b680ee8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha2 : a^2 + 2 * b = -2) (hb2 : b^2 + 4 * c = 2) : a^2 + 8 * c^2 ≥ 1 / 2   := by
  have helim0 : b = (-a^2/2 - 1) := by
    have hh := ha2
    linarith only [hh]
  have helim1 : c = (-a^4/16 - a^2/4 + 1/4) := by
    have hh := hb2
    try simp only [helim0] at hh
    linarith only [hh]
  have hsum : 0 ≤ (1/4 : ℝ) * (1) * (3*a^4/10 + a^2)^2 + (1/10 : ℝ) * (1) * (a^3)^2 + (7/800 : ℝ) * (1) * (a^4)^2 := by positivity
  have hid : ( a^2 + 8 * c^2 ) - ( 1 / 2   ) = (1/4 : ℝ) * (1) * (3*a^4/10 + a^2)^2 + (1/10 : ℝ) * (1) * (a^3)^2 + (7/800 : ℝ) * (1) * (a^4)^2 := by
    try simp only [helim0, helim1]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha2 : a^2 + 2 * b = -2) (hb2 : b^2 + 4 * c = 2), a^2 + 8 * c^2 ≥ 1 / 2) := @solution
#print axioms solution
