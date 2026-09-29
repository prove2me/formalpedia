-- Prove2me | solution 1 for WorkbookSource.base_7010
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:27:00.629644+00:00
-- url     : https://prove2.me/submissions/bfa8498e-4159-41a0-847c-cae3c075fc4d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y / (x ^ 2 + y * z + z * x) + y * z / (y ^ 2 + z * x + x * y) + z * x / (z ^ 2 + x * y + y * z)) ≤ (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6*y^2 + x^6*y*z + x^5*y^3 + x^5*y^2*z + x^5*y*z^2 - x^4*y^2*z^2 - 4*x^3*y^3*z^2 - 4*x^3*y^2*z^3 + x^3*z^5 + x^2*y^5*z - x^2*y^4*z^2 - 4*x^2*y^3*z^3 - x^2*y^2*z^4 + x^2*y*z^5 + x^2*z^6 + x*y^6*z + x*y^5*z^2 + x*y^2*z^5 + x*y*z^6 + y^6*z^2 + y^5*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (30 : ℝ) * x^6 * (y - x)^2 + (30 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (30 : ℝ) * x^6 * (z - y)^2 + (121 : ℝ) * x^5 * (y - x)^3 + (162 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (159 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (59 : ℝ) * x^5 * (z - y)^3 + (199 : ℝ) * x^4 * (y - x)^4 + (333 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (337 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (203 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (44 : ℝ) * x^4 * (z - y)^4 + (171 : ℝ) * x^3 * (y - x)^5 + (340 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (358 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (262 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (103 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (15 : ℝ) * x^3 * (z - y)^5 + (81 : ℝ) * x^2 * (y - x)^6 + (183 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (196 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (152 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (79 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (21 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (2 : ℝ) * x^2 * (z - y)^6 + (20 : ℝ) * x^1 * (y - x)^7 + (49 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (50 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (35 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (20 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (7 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (1 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (2 : ℝ) * (y - x)^8 + (5 : ℝ) * (y - x)^7 * (z - y)^1 + (4 : ℝ) * (y - x)^6 * (z - y)^2 + (1 : ℝ) * (y - x)^5 * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (x^6*y^2 + x^6*y*z + x^5*y^3 + x^5*y^2*z + x^5*y*z^2 - x^4*y^2*z^2 - 4*x^3*y^3*z^2 - 4*x^3*y^2*z^3 + x^3*z^5 + x^2*y^5*z - x^2*y^4*z^2 - 4*x^2*y^3*z^3 - x^2*y^2*z^4 + x^2*y*z^5 + x^2*z^6 + x*y^6*z + x*y^5*z^2 + x*y^2*z^5 + x*y*z^6 + y^6*z^2 + y^5*z^3) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (30 : ℝ) * x^6 * (z - x)^2 + (30 : ℝ) * x^6 * (z - x)^1 * (y - z)^1 + (30 : ℝ) * x^6 * (y - z)^2 + (121 : ℝ) * x^5 * (z - x)^3 + (201 : ℝ) * x^5 * (z - x)^2 * (y - z)^1 + (198 : ℝ) * x^5 * (z - x)^1 * (y - z)^2 + (59 : ℝ) * x^5 * (y - z)^3 + (199 : ℝ) * x^4 * (z - x)^4 + (463 : ℝ) * x^4 * (z - x)^3 * (y - z)^1 + (532 : ℝ) * x^4 * (z - x)^2 * (y - z)^2 + (268 : ℝ) * x^4 * (z - x)^1 * (y - z)^3 + (44 : ℝ) * x^4 * (y - z)^4 + (171 : ℝ) * x^3 * (z - x)^5 + (515 : ℝ) * x^3 * (z - x)^4 * (y - z)^1 + (708 : ℝ) * x^3 * (z - x)^3 * (y - z)^2 + (482 : ℝ) * x^3 * (z - x)^2 * (y - z)^3 + (148 : ℝ) * x^3 * (z - x)^1 * (y - z)^4 + (15 : ℝ) * x^3 * (y - z)^5 + (81 : ℝ) * x^2 * (z - x)^6 + (303 : ℝ) * x^2 * (z - x)^5 * (y - z)^1 + (496 : ℝ) * x^2 * (z - x)^4 * (y - z)^2 + (422 : ℝ) * x^2 * (z - x)^3 * (y - z)^3 + (184 : ℝ) * x^2 * (z - x)^2 * (y - z)^4 + (36 : ℝ) * x^2 * (z - x)^1 * (y - z)^5 + (2 : ℝ) * x^2 * (y - z)^6 + (20 : ℝ) * x^1 * (z - x)^7 + (91 : ℝ) * x^1 * (z - x)^6 * (y - z)^1 + (176 : ℝ) * x^1 * (z - x)^5 * (y - z)^2 + (180 : ℝ) * x^1 * (z - x)^4 * (y - z)^3 + (100 : ℝ) * x^1 * (z - x)^3 * (y - z)^4 + (28 : ℝ) * x^1 * (z - x)^2 * (y - z)^5 + (3 : ℝ) * x^1 * (z - x)^1 * (y - z)^6 + (2 : ℝ) * (z - x)^8 + (11 : ℝ) * (z - x)^7 * (y - z)^1 + (25 : ℝ) * (z - x)^6 * (y - z)^2 + (30 : ℝ) * (z - x)^5 * (y - z)^3 + (20 : ℝ) * (z - x)^4 * (y - z)^4 + (7 : ℝ) * (z - x)^3 * (y - z)^5 + (1 : ℝ) * (z - x)^2 * (y - z)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6*y^2 + x^6*y*z + x^5*y^3 + x^5*y^2*z + x^5*y*z^2 - x^4*y^2*z^2 - 4*x^3*y^3*z^2 - 4*x^3*y^2*z^3 + x^3*z^5 + x^2*y^5*z - x^2*y^4*z^2 - 4*x^2*y^3*z^3 - x^2*y^2*z^4 + x^2*y*z^5 + x^2*z^6 + x*y^6*z + x*y^5*z^2 + x*y^2*z^5 + x*y*z^6 + y^6*z^2 + y^5*z^3) := by
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
  have hn : 0 ≤ (x^6*y^2 + x^6*y*z + x^5*y^3 + x^5*y^2*z + x^5*y*z^2 - x^4*y^2*z^2 - 4*x^3*y^3*z^2 - 4*x^3*y^2*z^3 + x^3*z^5 + x^2*y^5*z - x^2*y^4*z^2 - 4*x^2*y^3*z^3 - x^2*y^2*z^4 + x^2*y*z^5 + x^2*z^6 + x*y^6*z + x*y^5*z^2 + x*y^2*z^5 + x*y*z^6 + y^6*z^2 + y^5*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x * y / (x ^ 2 + y * z + z * x) + y * z / (y ^ 2 + z * x + x * y) + z * x / (z ^ 2 + x * y + y * z)) ≤ (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x)) := @solution
#print axioms solution
