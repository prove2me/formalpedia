-- Prove2me | solution 1 for WorkbookSource.base_4249
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:11.398252+00:00
-- url     : https://prove2.me/submissions/c1635872-ad91-489c-9134-ae6f54bcdece

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x / (x + y) ^ 2 + y / (y + z) ^ 2 + z / (z + x) ^ 2) ≥ 1 / (x + y + z) + 10 * x * y * z / ((x + y) * (y + z) * (z + x) * (x + y + z))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*y + 3*x^4*y^2 + 3*x^4*y*z + 2*x^3*y^3 - 2*x^3*y^2*z - 4*x^3*y*z^2 + 2*x^3*z^3 - 4*x^2*y^3*z - 9*x^2*y^2*z^2 - 2*x^2*y*z^3 + 3*x^2*z^4 + 3*x*y^4*z - 2*x*y^3*z^2 - 4*x*y^2*z^3 + 3*x*y*z^4 + x*z^5 + y^5*z + 3*y^4*z^2 + 2*y^3*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (28 : ℝ) * x^4 * (y - x)^2 + (28 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (28 : ℝ) * x^4 * (z - y)^2 + (80 : ℝ) * x^3 * (y - x)^3 + (102 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (86 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (32 : ℝ) * x^3 * (z - y)^3 + (83 : ℝ) * x^2 * (y - x)^4 + (130 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (99 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (52 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (11 : ℝ) * x^2 * (z - y)^4 + (37 : ℝ) * x^1 * (y - x)^5 + (69 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (50 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (24 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (8 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (1 : ℝ) * x^1 * (z - y)^5 + (6 : ℝ) * (y - x)^6 + (13 : ℝ) * (y - x)^5 * (z - y)^1 + (9 : ℝ) * (y - x)^4 * (z - y)^2 + (2 : ℝ) * (y - x)^3 * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (x^5*y + 3*x^4*y^2 + 3*x^4*y*z + 2*x^3*y^3 - 2*x^3*y^2*z - 4*x^3*y*z^2 + 2*x^3*z^3 - 4*x^2*y^3*z - 9*x^2*y^2*z^2 - 2*x^2*y*z^3 + 3*x^2*z^4 + 3*x*y^4*z - 2*x*y^3*z^2 - 4*x*y^2*z^3 + 3*x*y*z^4 + x*z^5 + y^5*z + 3*y^4*z^2 + 2*y^3*z^3) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (28 : ℝ) * x^4 * (z - x)^2 + (28 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (28 : ℝ) * x^4 * (y - z)^2 + (80 : ℝ) * x^3 * (z - x)^3 + (138 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (122 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (32 : ℝ) * x^3 * (y - z)^3 + (83 : ℝ) * x^2 * (z - x)^4 + (202 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (207 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (88 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (11 : ℝ) * x^2 * (y - z)^4 + (37 : ℝ) * x^1 * (z - x)^5 + (116 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (144 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (82 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (19 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (1 : ℝ) * x^1 * (y - z)^5 + (6 : ℝ) * (z - x)^6 + (23 : ℝ) * (z - x)^5 * (y - z)^1 + (34 : ℝ) * (z - x)^4 * (y - z)^2 + (24 : ℝ) * (z - x)^3 * (y - z)^3 + (8 : ℝ) * (z - x)^2 * (y - z)^4 + (1 : ℝ) * (z - x)^1 * (y - z)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*y + 3*x^4*y^2 + 3*x^4*y*z + 2*x^3*y^3 - 2*x^3*y^2*z - 4*x^3*y*z^2 + 2*x^3*z^3 - 4*x^2*y^3*z - 9*x^2*y^2*z^2 - 2*x^2*y*z^3 + 3*x^2*z^4 + 3*x*y^4*z - 2*x*y^3*z^2 - 4*x*y^2*z^3 + 3*x*y*z^4 + x*z^5 + y^5*z + 3*y^4*z^2 + 2*y^3*z^3) := by
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
  have hn : 0 ≤ (x^5*y + 3*x^4*y^2 + 3*x^4*y*z + 2*x^3*y^3 - 2*x^3*y^2*z - 4*x^3*y*z^2 + 2*x^3*z^3 - 4*x^2*y^3*z - 9*x^2*y^2*z^2 - 2*x^2*y*z^3 + 3*x^2*z^4 + 3*x*y^4*z - 2*x*y^3*z^2 - 4*x*y^2*z^3 + 3*x*y*z^4 + x*z^5 + y^5*z + 3*y^4*z^2 + 2*y^3*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0), (x / (x + y) ^ 2 + y / (y + z) ^ 2 + z / (z + x) ^ 2) ≥ 1 / (x + y + z) + 10 * x * y * z / ((x + y) * (y + z) * (z + x) * (x + y + z))) := @solution
#print axioms solution
