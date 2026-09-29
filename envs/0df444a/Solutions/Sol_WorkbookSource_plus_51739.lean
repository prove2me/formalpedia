-- Prove2me | solution 1 for WorkbookSource.plus_51739
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:28:58.425799+00:00
-- url     : https://prove2.me/submissions/224fa425-c1fd-42ab-b291-2b7bbfc77cac

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 2 * y * z / x ^ 2 + 2 * x * z / y ^ 2 + 5 * x * y / z ^ 2 ≥ 3 * x / z + 3 * y / z + 3   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (5*x^3*y^3 - 3*x^3*y^2*z + 2*x^3*z^3 - 3*x^2*y^3*z - 3*x^2*y^2*z^2 + 2*y^3*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * x^4 * (y - x)^2 + (9 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (9 : ℝ) * x^4 * (z - y)^2 + (20 : ℝ) * x^3 * (y - x)^3 + (36 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (24 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (4 : ℝ) * x^3 * (z - y)^3 + (24 : ℝ) * x^2 * (y - x)^4 + (51 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (33 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (6 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (12 : ℝ) * x^1 * (y - x)^5 + (30 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (24 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (6 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (2 : ℝ) * (y - x)^6 + (6 : ℝ) * (y - x)^5 * (z - y)^1 + (6 : ℝ) * (y - x)^4 * (z - y)^2 + (2 : ℝ) * (y - x)^3 * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (5*x^3*y^3 - 3*x^3*y^2*z + 2*x^3*z^3 - 3*x^2*y^3*z - 3*x^2*y^2*z^2 + 2*y^3*z^3) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * x^4 * (z - x)^2 + (3 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (6 : ℝ) * x^4 * (y - z)^2 + (20 : ℝ) * x^3 * (z - x)^3 + (24 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (12 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (4 : ℝ) * x^3 * (y - z)^3 + (24 : ℝ) * x^2 * (z - x)^4 + (45 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (24 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (3 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (12 : ℝ) * x^1 * (z - x)^5 + (30 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (24 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (6 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (2 : ℝ) * (z - x)^6 + (6 : ℝ) * (z - x)^5 * (y - z)^1 + (6 : ℝ) * (z - x)^4 * (y - z)^2 + (2 : ℝ) * (z - x)^3 * (y - z)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (x y z : ℝ) (hlow : 0 ≤ z) (hord1 : z ≤ x) (hord2 : x ≤ y) : 0 ≤ (5*x^3*y^3 - 3*x^3*y^2*z + 2*x^3*z^3 - 3*x^2*y^3*z - 3*x^2*y^2*z^2 + 2*y^3*z^3) := by
    have hdiff1 : 0 ≤ (x - z) := by linarith
    have hdiff2 : 0 ≤ (y - x) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * z^4 * (x - z)^2 + (9 : ℝ) * z^4 * (x - z)^1 * (y - x)^1 + (6 : ℝ) * z^4 * (y - x)^2 + (32 : ℝ) * z^3 * (x - z)^3 + (48 : ℝ) * z^3 * (x - z)^2 * (y - x)^1 + (24 : ℝ) * z^3 * (x - z)^1 * (y - x)^2 + (4 : ℝ) * z^3 * (y - x)^3 + (42 : ℝ) * z^2 * (x - z)^4 + (84 : ℝ) * z^2 * (x - z)^3 * (y - x)^1 + (51 : ℝ) * z^2 * (x - z)^2 * (y - x)^2 + (9 : ℝ) * z^2 * (x - z)^1 * (y - x)^3 + (24 : ℝ) * z^1 * (x - z)^5 + (60 : ℝ) * z^1 * (x - z)^4 * (y - x)^1 + (48 : ℝ) * z^1 * (x - z)^3 * (y - x)^2 + (12 : ℝ) * z^1 * (x - z)^2 * (y - x)^3 + (5 : ℝ) * (x - z)^6 + (15 : ℝ) * (x - z)^5 * (y - x)^1 + (15 : ℝ) * (x - z)^4 * (y - x)^2 + (5 : ℝ) * (x - z)^3 * (y - x)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*x^3*y^3 - 3*x^3*y^2*z + 2*x^3*z^3 - 3*x^2*y^3*z - 3*x^2*y^2*z^2 + 2*y^3*z^3) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux1 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux0 y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux1 y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (5*x^3*y^3 - 3*x^3*y^2*z + 2*x^3*z^3 - 3*x^2*y^3*z - 3*x^2*y^2*z^2 + 2*y^3*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 2 * y * z / x ^ 2 + 2 * x * z / y ^ 2 + 5 * x * y / z ^ 2 ≥ 3 * x / z + 3 * y / z + 3) := @solution
#print axioms solution
