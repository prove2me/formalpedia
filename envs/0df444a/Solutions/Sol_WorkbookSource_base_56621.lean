-- Prove2me | solution 1 for WorkbookSource.base_56621
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:38:05.419465+00:00
-- url     : https://prove2.me/submissions/fe733679-6432-430b-a395-2f002fb019b4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 5) : x^2*y + z^2*x + x^2 + (y - 1)^2 + 2*x*y*z ≤ 32  := by
  have helim : z = (-x - y + 5) := by linarith only [h]
  have hslack : 0 ≤ (-x - y + 5) := by linarith only [helim, hz]
  have hsum : 0 ≤ (31/5 : ℝ) * ((-x - y + 5)) * (-1843*x/6076 + 131*y/992 + 1)^2 + (577187/1190896 : ℝ) * ((-x - y + 5)) * (x + 1191141*y/23087480)^2 + (1426207/461749600 : ℝ) * ((-x - y + 5)) * (y)^2 + (9/80 : ℝ) * ((y)) * (-x/3 + y + 1/3)^2 + (363/490 : ℝ) * ((x)) * (-3*x/11 + y + 1/11)^2 := by positivity
  have hid : ( 32  ) - ( x^2*y + z^2*x + x^2 + (y - 1)^2 + 2*x*y*z ) = (31/5 : ℝ) * ((-x - y + 5)) * (-1843*x/6076 + 131*y/992 + 1)^2 + (577187/1190896 : ℝ) * ((-x - y + 5)) * (x + 1191141*y/23087480)^2 + (1426207/461749600 : ℝ) * ((-x - y + 5)) * (y)^2 + (9/80 : ℝ) * ((y)) * (-x/3 + y + 1/3)^2 + (363/490 : ℝ) * ((x)) * (-3*x/11 + y + 1/11)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 5), x^2*y + z^2*x + x^2 + (y - 1)^2 + 2*x*y*z ≤ 32) := @solution
#print axioms solution
