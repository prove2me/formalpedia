-- Prove2me | solution 1 for WorkbookSource.base_6985
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:26:59.776153+00:00
-- url     : https://prove2.me/submissions/2ef918b1-c834-428f-ab5d-20c255bf7dba

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x^2 / (y^2 + z^2 + y * z) + y^2 / (z^2 + x^2 + z * x) + z^2 / (x^2 + y^2 + x * y)) ≥ 1  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6 + x^5*y + x^5*z - x^3*y^3 - x^3*y^2*z - x^3*y*z^2 - x^3*z^3 - x^2*y^3*z - x^2*y*z^3 + x*y^5 - x*y^3*z^2 - x*y^2*z^3 + x*z^5 + y^6 + y^5*z - y^3*z^3 + y*z^5 + z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * x^4 * (y - x)^2 + (21 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (21 : ℝ) * x^4 * (z - y)^2 + (48 : ℝ) * x^3 * (y - x)^3 + (72 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (96 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (36 : ℝ) * x^3 * (z - y)^3 + (43 : ℝ) * x^2 * (y - x)^4 + (86 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (147 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (104 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (25 : ℝ) * x^2 * (z - y)^4 + (18 : ℝ) * x^1 * (y - x)^5 + (45 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (94 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (96 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (45 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (8 : ℝ) * x^1 * (z - y)^5 + (3 : ℝ) * (y - x)^6 + (9 : ℝ) * (y - x)^5 * (z - y)^1 + (22 : ℝ) * (y - x)^4 * (z - y)^2 + (29 : ℝ) * (y - x)^3 * (z - y)^3 + (20 : ℝ) * (y - x)^2 * (z - y)^4 + (7 : ℝ) * (y - x)^1 * (z - y)^5 + (1 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6 + x^5*y + x^5*z - x^3*y^3 - x^3*y^2*z - x^3*y*z^2 - x^3*z^3 - x^2*y^3*z - x^2*y*z^3 + x*y^5 - x*y^3*z^2 - x*y^2*z^3 + x*z^5 + y^6 + y^5*z - y^3*z^3 + y*z^5 + z^6) := by
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
  have hn : 0 ≤ (x^6 + x^5*y + x^5*z - x^3*y^3 - x^3*y^2*z - x^3*y*z^2 - x^3*z^3 - x^2*y^3*z - x^2*y*z^3 + x*y^5 - x*y^3*z^2 - x*y^2*z^3 + x*z^5 + y^6 + y^5*z - y^3*z^3 + y*z^5 + z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0), (x^2 / (y^2 + z^2 + y * z) + y^2 / (z^2 + x^2 + z * x) + z^2 / (x^2 + y^2 + x * y)) ≥ 1) := @solution
#print axioms solution
