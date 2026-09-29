-- Prove2me | solution 1 for WorkbookSource.base_51967
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:15.625899+00:00
-- url     : https://prove2.me/submissions/986c5c98-14c7-433a-855e-199310176bef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 ≤ (x - y) * (x - 2 * y) / ((x + 2 * z) * (z + x)) + (y - z) * (y - 2 * z) / ((x + y) * (y + 2 * x)) + (z - x) * (z - 2 * x) / ((y + z) * (z + 2 * y))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (4*x^6 + 6*x^5*y + 6*x^5*z + 6*x^4*y^2 + 15*x^4*y*z - 6*x^4*z^2 - 6*x^3*y^3 - 6*x^3*y^2*z - 15*x^3*y*z^2 - 6*x^3*z^3 - 6*x^2*y^4 - 15*x^2*y^3*z - 12*x^2*y^2*z^2 - 6*x^2*y*z^3 + 6*x^2*z^4 + 6*x*y^5 + 15*x*y^4*z - 6*x*y^3*z^2 - 15*x*y^2*z^3 + 15*x*y*z^4 + 6*x*z^5 + 4*y^6 + 6*y^5*z + 6*y^4*z^2 - 6*y^3*z^3 - 6*y^2*z^4 + 6*y*z^5 + 4*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (138 : ℝ) * x^4 * (y - x)^2 + (138 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (138 : ℝ) * x^4 * (z - y)^2 + (325 : ℝ) * x^3 * (y - x)^3 + (435 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (564 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (227 : ℝ) * x^3 * (z - y)^3 + (282 : ℝ) * x^2 * (y - x)^4 + (459 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (735 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (558 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (135 : ℝ) * x^2 * (z - y)^4 + (105 : ℝ) * x^1 * (y - x)^5 + (198 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (387 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (435 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (213 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (36 : ℝ) * x^1 * (z - y)^5 + (14 : ℝ) * (y - x)^6 + (30 : ℝ) * (y - x)^5 * (z - y)^1 + (72 : ℝ) * (y - x)^4 * (z - y)^2 + (110 : ℝ) * (y - x)^3 * (z - y)^3 + (84 : ℝ) * (y - x)^2 * (z - y)^4 + (30 : ℝ) * (y - x)^1 * (z - y)^5 + (4 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (4*x^6 + 6*x^5*y + 6*x^5*z + 6*x^4*y^2 + 15*x^4*y*z - 6*x^4*z^2 - 6*x^3*y^3 - 6*x^3*y^2*z - 15*x^3*y*z^2 - 6*x^3*z^3 - 6*x^2*y^4 - 15*x^2*y^3*z - 12*x^2*y^2*z^2 - 6*x^2*y*z^3 + 6*x^2*z^4 + 6*x*y^5 + 15*x*y^4*z - 6*x*y^3*z^2 - 15*x*y^2*z^3 + 15*x*y*z^4 + 6*x*z^5 + 4*y^6 + 6*y^5*z + 6*y^4*z^2 - 6*y^3*z^3 - 6*y^2*z^4 + 6*y*z^5 + 4*z^6) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (138 : ℝ) * x^4 * (z - x)^2 + (138 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (138 : ℝ) * x^4 * (y - z)^2 + (325 : ℝ) * x^3 * (z - x)^3 + (540 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (669 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (227 : ℝ) * x^3 * (y - z)^3 + (282 : ℝ) * x^2 * (z - x)^4 + (669 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (1050 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (663 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (135 : ℝ) * x^2 * (y - z)^4 + (105 : ℝ) * x^1 * (z - x)^5 + (327 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (645 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (588 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (237 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (36 : ℝ) * x^1 * (y - z)^5 + (14 : ℝ) * (z - x)^6 + (54 : ℝ) * (z - x)^5 * (y - z)^1 + (132 : ℝ) * (z - x)^4 * (y - z)^2 + (158 : ℝ) * (z - x)^3 * (y - z)^3 + (96 : ℝ) * (z - x)^2 * (y - z)^4 + (30 : ℝ) * (z - x)^1 * (y - z)^5 + (4 : ℝ) * (y - z)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*x^6 + 6*x^5*y + 6*x^5*z + 6*x^4*y^2 + 15*x^4*y*z - 6*x^4*z^2 - 6*x^3*y^3 - 6*x^3*y^2*z - 15*x^3*y*z^2 - 6*x^3*z^3 - 6*x^2*y^4 - 15*x^2*y^3*z - 12*x^2*y^2*z^2 - 6*x^2*y*z^3 + 6*x^2*z^4 + 6*x*y^5 + 15*x*y^4*z - 6*x*y^3*z^2 - 15*x*y^2*z^3 + 15*x*y*z^4 + 6*x*z^5 + 4*y^6 + 6*y^5*z + 6*y^4*z^2 - 6*y^3*z^3 - 6*y^2*z^4 + 6*y*z^5 + 4*z^6) := by
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
  have hn : 0 ≤ (4*x^6 + 6*x^5*y + 6*x^5*z + 6*x^4*y^2 + 15*x^4*y*z - 6*x^4*z^2 - 6*x^3*y^3 - 6*x^3*y^2*z - 15*x^3*y*z^2 - 6*x^3*z^3 - 6*x^2*y^4 - 15*x^2*y^3*z - 12*x^2*y^2*z^2 - 6*x^2*y*z^3 + 6*x^2*z^4 + 6*x*y^5 + 15*x*y^4*z - 6*x*y^3*z^2 - 15*x*y^2*z^3 + 15*x*y*z^4 + 6*x*z^5 + 4*y^6 + 6*y^5*z + 6*y^4*z^2 - 6*y^3*z^3 - 6*y^2*z^4 + 6*y*z^5 + 4*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 0 ≤ (x - y) * (x - 2 * y) / ((x + 2 * z) * (z + x)) + (y - z) * (y - 2 * z) / ((x + y) * (y + 2 * x)) + (z - x) * (z - 2 * x) / ((y + z) * (z + 2 * y))) := @solution
#print axioms solution
