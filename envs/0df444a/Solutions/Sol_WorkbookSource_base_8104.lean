-- Prove2me | solution 1 for WorkbookSource.base_8104
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:52:09.057565+00:00
-- url     : https://prove2.me/submissions/b5b8351a-c8d9-489c-9135-b11b2f867952

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z t u : ℝ) (h₁ : x + y + z + t + u = 0) (h₂ : x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 + u ^ 2 = 20) : x ^ 4 + y ^ 4 + z ^ 4 + t ^ 4 + u ^ 4 ≤ 260  := by
  have helim : u = (-t - x - y - z) := by linarith only [h₁]
  have hw0 : 0 ≤ (2*t^2 + 2*t*x + 2*t*y + 2*t*z + 2*x^2 + 2*x*y + 2*x*z + 2*y^2 + 2*y*z + 2*z^2 - 20) := by
    have hh := h₂
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20) := by
    have hh := h₂
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (11/5 : ℝ) * (1) * (3*t^2/11 - t*x/11 - t*y/11 + t*z - 3*x^2/11 - 7*x*y/11 - x*z/11 - 3*y^2/11 - y*z/11 + 3*z^2/11)^2 + (24/11 : ℝ) * (1) * (3*t^2/10 - t*x/10 + t*y - 3*x^2/10 - 3*x*y/20 - 13*x*z/20 + y^2/4 - y*z/10 - z^2/4)^2 + (54/25 : ℝ) * (1) * (-2*t^2/9 - 2*t*x/3 - x^2/3 - x*y/6 - x*z/6 + 5*y^2/18 + y*z + 5*z^2/18)^2 + (6/5 : ℝ) * (1) * (t^2/3 + t*x - x*y/2 - x*z/2 - y^2/6 - z^2/6)^2 + (9/10 : ℝ) * (1) * (-x*y + x*z - y^2/3 + z^2/3)^2 + (13 : ℝ) * ((-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20)) * (1)^2 + (13/10 : ℝ) * ((-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20)) * (t + x/2 + y/2 + z/2)^2 + (39/40 : ℝ) * ((-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20)) * (x/3 + y/3 + z)^2 + (13/15 : ℝ) * ((-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20)) * (x/4 + y)^2 + (13/16 : ℝ) * ((-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20)) * (x)^2 := by positivity
  have hid : ( 260  ) - ( x ^ 4 + y ^ 4 + z ^ 4 + t ^ 4 + u ^ 4 ) = (11/5 : ℝ) * (1) * (3*t^2/11 - t*x/11 - t*y/11 + t*z - 3*x^2/11 - 7*x*y/11 - x*z/11 - 3*y^2/11 - y*z/11 + 3*z^2/11)^2 + (24/11 : ℝ) * (1) * (3*t^2/10 - t*x/10 + t*y - 3*x^2/10 - 3*x*y/20 - 13*x*z/20 + y^2/4 - y*z/10 - z^2/4)^2 + (54/25 : ℝ) * (1) * (-2*t^2/9 - 2*t*x/3 - x^2/3 - x*y/6 - x*z/6 + 5*y^2/18 + y*z + 5*z^2/18)^2 + (6/5 : ℝ) * (1) * (t^2/3 + t*x - x*y/2 - x*z/2 - y^2/6 - z^2/6)^2 + (9/10 : ℝ) * (1) * (-x*y + x*z - y^2/3 + z^2/3)^2 + (13 : ℝ) * ((-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20)) * (1)^2 + (13/10 : ℝ) * ((-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20)) * (t + x/2 + y/2 + z/2)^2 + (39/40 : ℝ) * ((-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20)) * (x/3 + y/3 + z)^2 + (13/15 : ℝ) * ((-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20)) * (x/4 + y)^2 + (13/16 : ℝ) * ((-2*t^2 - 2*t*x - 2*t*y - 2*t*z - 2*x^2 - 2*x*y - 2*x*z - 2*y^2 - 2*y*z - 2*z^2 + 20)) * (x)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y z t u : ℝ) (h₁ : x + y + z + t + u = 0) (h₂ : x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 + u ^ 2 = 20), x ^ 4 + y ^ 4 + z ^ 4 + t ^ 4 + u ^ 4 ≤ 260) := @solution
#print axioms solution
