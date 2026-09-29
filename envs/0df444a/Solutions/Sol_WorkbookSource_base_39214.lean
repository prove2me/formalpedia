-- Prove2me | solution 1 for WorkbookSource.base_39214
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:44:57.405768+00:00
-- url     : https://prove2.me/submissions/4a8cd296-dcbb-4b2c-af3e-03a559d1f6b3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (1 + x * y) / (2 + x + x * y) + (1 + y * z) / (2 + y + y * z) + (1 + z * x) / (2 + z + z * x) ≤ 3 / 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (4*x^6/243 + 8*x^5*y/81 + 8*x^5*z/81 + 20*x^4*y^2/81 + 22*x^4*y*z/81 + 20*x^4*z^2/81 + 80*x^3*y^3/243 - x^3*y^2*z/81 - x^3*y*z^2/81 + 80*x^3*z^3/243 + 20*x^2*y^4/81 - x^2*y^3*z/81 - 104*x^2*y^2*z^2/27 - x^2*y*z^3/81 + 20*x^2*z^4/81 + 8*x*y^5/81 + 22*x*y^4*z/81 - x*y^3*z^2/81 - x*y^2*z^3/81 + 22*x*y*z^4/81 + 8*x*z^5/81 + 4*y^6/243 + 8*y^5*z/81 + 20*y^4*z^2/81 + 80*y^3*z^3/243 + 20*y^2*z^4/81 + 8*y*z^5/81 + 4*z^6/243) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * x^4 * (y - x)^2 + (16/3 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (16/3 : ℝ) * x^4 * (z - y)^2 + (46/3 : ℝ) * x^3 * (y - x)^3 + (23 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (59/3 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (6 : ℝ) * x^3 * (z - y)^3 + (16 : ℝ) * x^2 * (y - x)^4 + (32 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (29 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (13 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (2 : ℝ) * x^2 * (z - y)^4 + (190/27 : ℝ) * x^1 * (y - x)^5 + (475/27 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (496/27 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (269/27 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (74/27 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (8/27 : ℝ) * x^1 * (z - y)^5 + (256/243 : ℝ) * (y - x)^6 + (256/81 : ℝ) * (y - x)^5 * (z - y)^1 + (320/81 : ℝ) * (y - x)^4 * (z - y)^2 + (640/243 : ℝ) * (y - x)^3 * (z - y)^3 + (80/81 : ℝ) * (y - x)^2 * (z - y)^4 + (16/81 : ℝ) * (y - x)^1 * (z - y)^5 + (4/243 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*x^6/243 + 8*x^5*y/81 + 8*x^5*z/81 + 20*x^4*y^2/81 + 22*x^4*y*z/81 + 20*x^4*z^2/81 + 80*x^3*y^3/243 - x^3*y^2*z/81 - x^3*y*z^2/81 + 80*x^3*z^3/243 + 20*x^2*y^4/81 - x^2*y^3*z/81 - 104*x^2*y^2*z^2/27 - x^2*y*z^3/81 + 20*x^2*z^4/81 + 8*x*y^5/81 + 22*x*y^4*z/81 - x*y^3*z^2/81 - x*y^2*z^3/81 + 22*x*y*z^4/81 + 8*x*z^5/81 + 4*y^6/243 + 8*y^5*z/81 + 20*y^4*z^2/81 + 80*y^3*z^3/243 + 20*y^2*z^4/81 + 8*y*z^5/81 + 4*z^6/243) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux0 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux0 y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux0 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-3*x^2*y^2*z^2 - x^2*y^2*z - x^2*y*z^2 - 3*x^2*y*z - x*y^2*z^2 - 3*x*y^2*z - 3*x*y*z^2 + 3*x*y*z + 4*x + 4*y + 4*z) = (4*x^6/243 + 8*x^5*y/81 + 8*x^5*z/81 + 20*x^4*y^2/81 + 22*x^4*y*z/81 + 20*x^4*z^2/81 + 80*x^3*y^3/243 - x^3*y^2*z/81 - x^3*y*z^2/81 + 80*x^3*z^3/243 + 20*x^2*y^4/81 - x^2*y^3*z/81 - 104*x^2*y^2*z^2/27 - x^2*y*z^3/81 + 20*x^2*z^4/81 + 8*x*y^5/81 + 22*x*y^4*z/81 - x*y^3*z^2/81 - x*y^2*z^3/81 + 22*x*y*z^4/81 + 8*x*z^5/81 + 4*y^6/243 + 8*y^5*z/81 + 20*y^4*z^2/81 + 80*y^3*z^3/243 + 20*y^2*z^4/81 + 8*y*z^5/81 + 4*z^6/243) := by
    linear_combination (-4*x^5/243 - 20*x^4*y/243 - 20*x^4*z/243 - 4*x^4/81 - 40*x^3*y^2/243 - 26*x^3*y*z/243 - 16*x^3*y/81 - 40*x^3*z^2/243 - 16*x^3*z/81 - 4*x^3/27 - 40*x^2*y^3/243 + 23*x^2*y^2*z/81 - 8*x^2*y^2/27 + 23*x^2*y*z^2/81 + 2*x^2*y*z/27 - 4*x^2*y/9 - 40*x^2*z^3/243 - 8*x^2*z^2/27 - 4*x^2*z/9 - 4*x^2/9 - 20*x*y^4/243 - 26*x*y^3*z/243 - 16*x*y^3/81 + 23*x*y^2*z^2/81 + 2*x*y^2*z/27 - 4*x*y^2/9 - 26*x*y*z^3/243 + 2*x*y*z^2/27 - 17*x*y*z/9 - 8*x*y/9 - 20*x*z^4/243 - 16*x*z^3/81 - 4*x*z^2/9 - 8*x*z/9 - 4*x/3 - 4*y^5/243 - 20*y^4*z/243 - 4*y^4/81 - 40*y^3*z^2/243 - 16*y^3*z/81 - 4*y^3/27 - 40*y^2*z^3/243 - 8*y^2*z^2/27 - 4*y^2*z/9 - 4*y^2/9 - 20*y*z^4/243 - 16*y*z^3/81 - 4*y*z^2/9 - 8*y*z/9 - 4*y/3 - 4*z^5/243 - 4*z^4/81 - 4*z^3/27 - 4*z^2/9 - 4*z/3) * h
  have hn : 0 ≤ (-3*x^2*y^2*z^2 - x^2*y^2*z - x^2*y*z^2 - 3*x^2*y*z - x*y^2*z^2 - 3*x*y^2*z - 3*x*y*z^2 + 3*x*y*z + 4*x + 4*y + 4*z) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), (1 + x * y) / (2 + x + x * y) + (1 + y * z) / (2 + y + y * z) + (1 + z * x) / (2 + z + z * x) ≤ 3 / 2) := @solution
#print axioms solution
