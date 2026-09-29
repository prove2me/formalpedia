-- Prove2me | solution 1 for WorkbookSource.base_20269
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:27.845826+00:00
-- url     : https://prove2.me/submissions/3b328c24-ccbf-4881-9d3c-99d1fce3f9d1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) ^ 4 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) ≥ 81 * x ^ 2 * y ^ 2 * z ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2)  := by
  have haux (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6*y^2 + x^6*z^2 + 4*x^5*y^3 + 4*x^5*y^2*z + 4*x^5*y*z^2 + 4*x^5*z^3 + 6*x^4*y^4 + 12*x^4*y^3*z - 68*x^4*y^2*z^2 + 12*x^4*y*z^3 + 6*x^4*z^4 + 4*x^3*y^5 + 12*x^3*y^4*z + 20*x^3*y^3*z^2 + 20*x^3*y^2*z^3 + 12*x^3*y*z^4 + 4*x^3*z^5 + x^2*y^6 + 4*x^2*y^5*z - 68*x^2*y^4*z^2 + 20*x^2*y^3*z^3 - 68*x^2*y^2*z^4 + 4*x^2*y*z^5 + x^2*z^6 + 4*x*y^5*z^2 + 12*x*y^4*z^3 + 12*x*y^3*z^4 + 4*x*y^2*z^5 + y^6*z^2 + 4*y^5*z^3 + 6*y^4*z^4 + 4*y^3*z^5 + y^2*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (108 : ℝ) * x^6 * (y - x)^2 + (108 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (108 : ℝ) * x^6 * (z - y)^2 + (504 : ℝ) * x^5 * (y - x)^3 + (756 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (540 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (144 : ℝ) * x^5 * (z - y)^3 + (978 : ℝ) * x^4 * (y - x)^4 + (1956 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (1494 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (516 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (78 : ℝ) * x^4 * (z - y)^4 + (1004 : ℝ) * x^3 * (y - x)^5 + (2510 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (2348 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (1012 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (226 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (28 : ℝ) * x^3 * (z - y)^5 + (566 : ℝ) * x^2 * (y - x)^6 + (1698 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (1959 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (1088 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (309 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (48 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (2 : ℝ) * x^2 * (z - y)^6 + (160 : ℝ) * x^1 * (y - x)^7 + (560 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (776 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (540 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (196 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (34 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (2 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (16 : ℝ) * (y - x)^8 + (64 : ℝ) * (y - x)^7 * (z - y)^1 + (104 : ℝ) * (y - x)^6 * (z - y)^2 + (88 : ℝ) * (y - x)^5 * (z - y)^3 + (41 : ℝ) * (y - x)^4 * (z - y)^4 + (10 : ℝ) * (y - x)^3 * (z - y)^5 + (1 : ℝ) * (y - x)^2 * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6*y^2 + x^6*z^2 + 4*x^5*y^3 + 4*x^5*y^2*z + 4*x^5*y*z^2 + 4*x^5*z^3 + 6*x^4*y^4 + 12*x^4*y^3*z - 68*x^4*y^2*z^2 + 12*x^4*y*z^3 + 6*x^4*z^4 + 4*x^3*y^5 + 12*x^3*y^4*z + 20*x^3*y^3*z^2 + 20*x^3*y^2*z^3 + 12*x^3*y*z^4 + 4*x^3*z^5 + x^2*y^6 + 4*x^2*y^5*z - 68*x^2*y^4*z^2 + 20*x^2*y^3*z^3 - 68*x^2*y^2*z^4 + 4*x^2*y*z^5 + x^2*z^6 + 4*x*y^5*z^2 + 12*x*y^4*z^3 + 12*x*y^3*z^4 + 4*x*y^2*z^5 + y^6*z^2 + 4*y^5*z^3 + 6*y^4*z^4 + 4*y^3*z^5 + y^2*z^6) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0), (x + y + z) ^ 4 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) ≥ 81 * x ^ 2 * y ^ 2 * z ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2)) := @solution
#print axioms solution
