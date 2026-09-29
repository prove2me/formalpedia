-- Prove2me | solution 1 for WorkbookSource.base_35726
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:06:07.115973+00:00
-- url     : https://prove2.me/submissions/61cbd735-b999-4c81-b52b-9432aba8fc82

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y) / (x ^ 2 + x * y + y * z) + (y * z) / (y ^ 2 + y * z + z * x) + (z * x) / (z ^ 2 + z * x + x * y) ≤ 1  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^4*y*z + x^3*y^3 - 2*x^3*y*z^2 + x^3*z^3 - 2*x^2*y^3*z + x*y^4*z - 2*x*y^2*z^3 + x*y*z^4 + y^3*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * x^4 * (y - x)^2 + (4 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (4 : ℝ) * x^4 * (z - y)^2 + (12 : ℝ) * x^3 * (y - x)^3 + (17 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (13 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (4 : ℝ) * x^3 * (z - y)^3 + (13 : ℝ) * x^2 * (y - x)^4 + (24 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (18 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (7 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (1 : ℝ) * x^2 * (z - y)^4 + (6 : ℝ) * x^1 * (y - x)^5 + (14 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (12 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (5 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (1 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (1 : ℝ) * (y - x)^6 + (3 : ℝ) * (y - x)^5 * (z - y)^1 + (3 : ℝ) * (y - x)^4 * (z - y)^2 + (1 : ℝ) * (y - x)^3 * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (x^4*y*z + x^3*y^3 - 2*x^3*y*z^2 + x^3*z^3 - 2*x^2*y^3*z + x*y^4*z - 2*x*y^2*z^3 + x*y*z^4 + y^3*z^3) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * x^4 * (z - x)^2 + (4 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (4 : ℝ) * x^4 * (y - z)^2 + (12 : ℝ) * x^3 * (z - x)^3 + (19 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (15 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (4 : ℝ) * x^3 * (y - z)^3 + (13 : ℝ) * x^2 * (z - x)^4 + (28 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (24 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (9 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (1 : ℝ) * x^2 * (y - z)^4 + (6 : ℝ) * x^1 * (z - x)^5 + (16 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (16 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (7 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (1 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (1 : ℝ) * (z - x)^6 + (3 : ℝ) * (z - x)^5 * (y - z)^1 + (3 : ℝ) * (z - x)^4 * (y - z)^2 + (1 : ℝ) * (z - x)^3 * (y - z)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^4*y*z + x^3*y^3 - 2*x^3*y*z^2 + x^3*z^3 - 2*x^2*y^3*z + x*y^4*z - 2*x*y^2*z^3 + x*y*z^4 + y^3*z^3) := by
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
  have hn : 0 ≤ (x^4*y*z + x^3*y^3 - 2*x^3*y*z^2 + x^3*z^3 - 2*x^2*y^3*z + x*y^4*z - 2*x*y^2*z^3 + x*y*z^4 + y^3*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x * y) / (x ^ 2 + x * y + y * z) + (y * z) / (y ^ 2 + y * z + z * x) + (z * x) / (z ^ 2 + z * x + x * y) ≤ 1) := @solution
#print axioms solution
