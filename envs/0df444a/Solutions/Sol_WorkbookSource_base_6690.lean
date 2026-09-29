-- Prove2me | solution 1 for WorkbookSource.base_6690
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:23:54.949012+00:00
-- url     : https://prove2.me/submissions/4d9cff91-efc7-4d1a-a458-3caaf483043d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (x^3 + 4)/(x + 2) + (y^3 + 4)/(y + 2) + (z^3 + 4)/(z + 2) ≥ 5  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (104*x^5/243 + 304*x^4*y/243 + 304*x^4*z/243 + 68*x^3*y^2/243 + 190*x^3*y*z/243 + 68*x^3*z^2/243 + 68*x^2*y^3/243 - 346*x^2*y^2*z/81 - 346*x^2*y*z^2/81 + 68*x^2*z^3/243 + 304*x*y^4/243 + 190*x*y^3*z/243 - 346*x*y^2*z^2/81 + 190*x*y*z^3/243 + 304*x*z^4/243 + 104*y^5/243 + 304*y^4*z/243 + 68*y^3*z^2/243 + 68*y^2*z^3/243 + 304*y*z^4/243 + 104*z^5/243) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (46/3 : ℝ) * x^3 * (y - x)^2 + (46/3 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (46/3 : ℝ) * x^3 * (z - y)^2 + (820/27 : ℝ) * x^2 * (y - x)^3 + (410/9 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (418/9 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (422/27 : ℝ) * x^2 * (z - y)^3 + (1570/81 : ℝ) * x^1 * (y - x)^4 + (3140/81 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (1196/27 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (2018/81 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (376/81 : ℝ) * x^1 * (z - y)^4 + (952/243 : ℝ) * (y - x)^5 + (2380/243 : ℝ) * (y - x)^4 * (z - y)^1 + (3136/243 : ℝ) * (y - x)^3 * (z - y)^2 + (2324/243 : ℝ) * (y - x)^2 * (z - y)^3 + (824/243 : ℝ) * (y - x)^1 * (z - y)^4 + (104/243 : ℝ) * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (104*x^5/243 + 304*x^4*y/243 + 304*x^4*z/243 + 68*x^3*y^2/243 + 190*x^3*y*z/243 + 68*x^3*z^2/243 + 68*x^2*y^3/243 - 346*x^2*y^2*z/81 - 346*x^2*y*z^2/81 + 68*x^2*z^3/243 + 304*x*y^4/243 + 190*x*y^3*z/243 - 346*x*y^2*z^2/81 + 190*x*y*z^3/243 + 304*x*z^4/243 + 104*y^5/243 + 304*y^4*z/243 + 68*y^3*z^2/243 + 68*y^2*z^3/243 + 304*y*z^4/243 + 104*z^5/243) := by
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
  have he : (x^3*y*z + 2*x^3*y + 2*x^3*z + 4*x^3 + x*y^3*z + 2*x*y^3 + x*y*z^3 - 5*x*y*z - 6*x*y + 2*x*z^3 - 6*x*z - 4*x + 2*y^3*z + 4*y^3 + 2*y*z^3 - 6*y*z - 4*y + 4*z^3 - 4*z + 8) = (104*x^5/243 + 304*x^4*y/243 + 304*x^4*z/243 + 68*x^3*y^2/243 + 190*x^3*y*z/243 + 68*x^3*z^2/243 + 68*x^2*y^3/243 - 346*x^2*y^2*z/81 - 346*x^2*y*z^2/81 + 68*x^2*z^3/243 + 304*x*y^4/243 + 190*x*y^3*z/243 - 346*x*y^2*z^2/81 + 190*x*y*z^3/243 + 304*x*z^4/243 + 104*y^5/243 + 304*y^4*z/243 + 68*y^3*z^2/243 + 68*y^2*z^3/243 + 304*y*z^4/243 + 104*z^5/243) := by
    linear_combination (-104*x^4/243 - 200*x^3*y/243 - 200*x^3*z/243 - 104*x^3/81 + 44*x^2*y^2/81 + 151*x^2*y*z/81 + 22*x^2*y/27 + 44*x^2*z^2/81 + 22*x^2*z/27 + 4*x^2/27 - 200*x*y^3/243 + 151*x*y^2*z/81 + 22*x*y^2/27 + 151*x*y*z^2/81 + 107*x*y*z/27 + 62*x*y/27 - 200*x*z^3/243 + 22*x*z^2/27 + 62*x*z/27 + 4*x/9 - 104*y^4/243 - 200*y^3*z/243 - 104*y^3/81 + 44*y^2*z^2/81 + 22*y^2*z/27 + 4*y^2/27 - 200*y*z^3/243 + 22*y*z^2/27 + 62*y*z/27 + 4*y/9 - 104*z^4/243 - 104*z^3/81 + 4*z^2/27 + 4*z/9 - 8/3) * h
  have hn : 0 ≤ (x^3*y*z + 2*x^3*y + 2*x^3*z + 4*x^3 + x*y^3*z + 2*x*y^3 + x*y*z^3 - 5*x*y*z - 6*x*y + 2*x*z^3 - 6*x*z - 4*x + 2*y^3*z + 4*y^3 + 2*y*z^3 - 6*y*z - 4*y + 4*z^3 - 4*z + 8) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), (x^3 + 4)/(x + 2) + (y^3 + 4)/(y + 2) + (z^3 + 4)/(z + 2) ≥ 5) := @solution
#print axioms solution
