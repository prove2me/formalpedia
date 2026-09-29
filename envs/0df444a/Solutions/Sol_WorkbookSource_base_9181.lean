-- Prove2me | solution 1 for WorkbookSource.base_9181
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:40:44.374042+00:00
-- url     : https://prove2.me/submissions/cbe805fd-2857-44d5-98ef-941d6aa2b8bf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hx1 : x + y + z = 3) : (x * y) / (y + 1) + (y * z) / (z + 1) + (z * x) / (x + 1) ≥ (3 * x * y * z) / 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (8*x^5*y/81 + 2*x^5*z/81 + 26*x^4*y^2/81 + 4*x^4*y*z/9 + 14*x^4*z^2/81 + 10*x^3*y^3/27 + 5*x^3*y^2*z/81 - x^3*y*z^2/81 + 10*x^3*z^3/27 + 14*x^2*y^4/81 - x^2*y^3*z/81 - 40*x^2*y^2*z^2/9 + 5*x^2*y*z^3/81 + 26*x^2*z^4/81 + 2*x*y^5/81 + 4*x*y^4*z/9 + 5*x*y^3*z^2/81 - x*y^2*z^3/81 + 4*x*y*z^4/9 + 8*x*z^5/81 + 8*y^5*z/81 + 26*y^4*z^2/81 + 10*y^3*z^3/27 + 14*y^2*z^4/81 + 2*y*z^5/81) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * x^4 * (y - x)^2 + (16/3 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (16/3 : ℝ) * x^4 * (z - y)^2 + (140/9 : ℝ) * x^3 * (y - x)^3 + (67/3 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (55/3 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (52/9 : ℝ) * x^3 * (z - y)^3 + (146/9 : ℝ) * x^2 * (y - x)^4 + (274/9 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (25 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (97/9 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (14/9 : ℝ) * x^2 * (z - y)^4 + (566/81 : ℝ) * x^1 * (y - x)^5 + (1307/81 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (1178/81 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (541/81 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (124/81 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (10/81 : ℝ) * x^1 * (z - y)^5 + (80/81 : ℝ) * (y - x)^6 + (8/3 : ℝ) * (y - x)^5 * (z - y)^1 + (220/81 : ℝ) * (y - x)^4 * (z - y)^2 + (106/81 : ℝ) * (y - x)^3 * (z - y)^3 + (8/27 : ℝ) * (y - x)^2 * (z - y)^4 + (2/81 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (8*x^5*y/81 + 2*x^5*z/81 + 26*x^4*y^2/81 + 4*x^4*y*z/9 + 14*x^4*z^2/81 + 10*x^3*y^3/27 + 5*x^3*y^2*z/81 - x^3*y*z^2/81 + 10*x^3*z^3/27 + 14*x^2*y^4/81 - x^2*y^3*z/81 - 40*x^2*y^2*z^2/9 + 5*x^2*y*z^3/81 + 26*x^2*z^4/81 + 2*x*y^5/81 + 4*x*y^4*z/9 + 5*x*y^3*z^2/81 - x*y^2*z^3/81 + 4*x*y*z^4/9 + 8*x*z^5/81 + 8*y^5*z/81 + 26*y^4*z^2/81 + 10*y^3*z^3/27 + 14*y^2*z^4/81 + 2*y*z^5/81) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * x^4 * (z - x)^2 + (16/3 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (16/3 : ℝ) * x^4 * (y - z)^2 + (140/9 : ℝ) * x^3 * (z - x)^3 + (73/3 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (61/3 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (52/9 : ℝ) * x^3 * (y - z)^3 + (146/9 : ℝ) * x^2 * (z - x)^4 + (310/9 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (31 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (115/9 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (14/9 : ℝ) * x^2 * (y - z)^4 + (566/81 : ℝ) * x^1 * (z - x)^5 + (1523/81 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (1610/81 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (811/81 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (178/81 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (10/81 : ℝ) * x^1 * (y - z)^5 + (80/81 : ℝ) * (z - x)^6 + (88/27 : ℝ) * (z - x)^5 * (y - z)^1 + (340/81 : ℝ) * (z - x)^4 * (y - z)^2 + (214/81 : ℝ) * (z - x)^3 * (y - z)^3 + (22/27 : ℝ) * (z - x)^2 * (y - z)^4 + (8/81 : ℝ) * (z - x)^1 * (y - z)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*x^5*y/81 + 2*x^5*z/81 + 26*x^4*y^2/81 + 4*x^4*y*z/9 + 14*x^4*z^2/81 + 10*x^3*y^3/27 + 5*x^3*y^2*z/81 - x^3*y*z^2/81 + 10*x^3*z^3/27 + 14*x^2*y^4/81 - x^2*y^3*z/81 - 40*x^2*y^2*z^2/9 + 5*x^2*y*z^3/81 + 26*x^2*z^4/81 + 2*x*y^5/81 + 4*x*y^4*z/9 + 5*x*y^3*z^2/81 - x*y^2*z^3/81 + 4*x*y*z^4/9 + 8*x*z^5/81 + 8*y^5*z/81 + 26*y^4*z^2/81 + 10*y^3*z^3/27 + 14*y^2*z^4/81 + 2*y*z^5/81) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux1 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux1 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux0 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-3*x^2*y^2*z^2 - 3*x^2*y^2*z - 3*x^2*y*z^2 - x^2*y*z + 2*x^2*y - 3*x*y^2*z^2 - x*y^2*z - x*y*z^2 + 3*x*y*z + 2*x*y + 2*x*z^2 + 2*x*z + 2*y^2*z + 2*y*z) = (8*x^5*y/81 + 2*x^5*z/81 + 26*x^4*y^2/81 + 4*x^4*y*z/9 + 14*x^4*z^2/81 + 10*x^3*y^3/27 + 5*x^3*y^2*z/81 - x^3*y*z^2/81 + 10*x^3*z^3/27 + 14*x^2*y^4/81 - x^2*y^3*z/81 - 40*x^2*y^2*z^2/9 + 5*x^2*y*z^3/81 + 26*x^2*z^4/81 + 2*x*y^5/81 + 4*x*y^4*z/9 + 5*x*y^3*z^2/81 - x*y^2*z^3/81 + 4*x*y*z^4/9 + 8*x*z^5/81 + 8*y^5*z/81 + 26*y^4*z^2/81 + 10*y^3*z^3/27 + 14*y^2*z^4/81 + 2*y*z^5/81) := by
    linear_combination (-8*x^4*y/81 - 2*x^4*z/81 - 2*x^3*y^2/9 - 26*x^3*y*z/81 - 8*x^3*y/27 - 4*x^3*z^2/27 - 2*x^3*z/27 - 4*x^2*y^3/27 + 13*x^2*y^2*z/27 - 10*x^2*y^2/27 + 13*x^2*y*z^2/27 - 16*x^2*y*z/27 - 8*x^2*y/9 - 2*x^2*z^3/9 - 10*x^2*z^2/27 - 2*x^2*z/9 - 2*x*y^4/81 - 26*x*y^3*z/81 - 2*x*y^3/27 + 13*x*y^2*z^2/27 - 16*x*y^2*z/27 - 2*x*y^2/9 - 26*x*y*z^3/81 - 16*x*y*z^2/27 - 5*x*y*z/3 - 2*x*y/3 - 8*x*z^4/81 - 8*x*z^3/27 - 8*x*z^2/9 - 2*x*z/3 - 8*y^4*z/81 - 2*y^3*z^2/9 - 8*y^3*z/27 - 4*y^2*z^3/27 - 10*y^2*z^2/27 - 8*y^2*z/9 - 2*y*z^4/81 - 2*y*z^3/27 - 2*y*z^2/9 - 2*y*z/3) * hx1
  have hn : 0 ≤ (-3*x^2*y^2*z^2 - 3*x^2*y^2*z - 3*x^2*y*z^2 - x^2*y*z + 2*x^2*y - 3*x*y^2*z^2 - x*y^2*z - x*y*z^2 + 3*x*y*z + 2*x*y + 2*x*z^2 + 2*x*z + 2*y^2*z + 2*y*z) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hx1 : x + y + z = 3), (x * y) / (y + 1) + (y * z) / (z + 1) + (z * x) / (x + 1) ≥ (3 * x * y * z) / 2) := @solution
#print axioms solution
