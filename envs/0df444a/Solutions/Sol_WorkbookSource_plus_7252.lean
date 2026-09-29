-- Prove2me | solution 1 for WorkbookSource.plus_7252
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:44:32.053192+00:00
-- url     : https://prove2.me/submissions/c86f0d54-6b0e-4475-b255-2c0c5aa70cb2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 / (y + z)^2 + y^2 / (z + x)^2 + z^2 / (x + y)^2) ≥ 1 / 225 * (47 * x^2 - 22 * x * y - 22 * x * z + 47 * y^2 - 22 * y * z + 47 * z^2) * (x^2 + y^2 + z^2 + 3 * x * y + 3 * y * z + 3 * x * z)^2 / ((y + z)^2 * (z + x)^2 * (x + y)^2)   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (178*x^6 + 190*x^5*y + 190*x^5*z - 207*x^4*y^2 + 58*x^4*y*z - 207*x^4*z^2 - 322*x^3*y^3 - 58*x^3*y^2*z - 58*x^3*y*z^2 - 322*x^3*z^3 - 207*x^2*y^4 - 58*x^2*y^3*z + 708*x^2*y^2*z^2 - 58*x^2*y*z^3 - 207*x^2*z^4 + 190*x*y^5 + 58*x*y^4*z - 58*x*y^3*z^2 - 58*x*y^2*z^3 + 58*x*y*z^4 + 190*x*z^5 + 178*y^6 + 190*y^5*z - 207*y^4*z^2 - 322*y^3*z^3 - 207*y^2*z^4 + 190*y*z^5 + 178*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (2232 : ℝ) * x^4 * (y - x)^2 + (2232 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (2232 : ℝ) * x^4 * (z - y)^2 + (3752 : ℝ) * x^3 * (y - x)^3 + (5628 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (12228 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (5176 : ℝ) * x^3 * (z - y)^3 + (2078 : ℝ) * x^2 * (y - x)^4 + (4156 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (18270 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (16192 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (4214 : ℝ) * x^2 * (z - y)^4 + (380 : ℝ) * x^1 * (y - x)^5 + (950 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (10636 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (15004 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (7834 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (1448 : ℝ) * x^1 * (z - y)^5 + (2155 : ℝ) * (y - x)^4 * (z - y)^2 + (4310 : ℝ) * (y - x)^3 * (z - y)^3 + (3413 : ℝ) * (y - x)^2 * (z - y)^4 + (1258 : ℝ) * (y - x)^1 * (z - y)^5 + (178 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (178*x^6 + 190*x^5*y + 190*x^5*z - 207*x^4*y^2 + 58*x^4*y*z - 207*x^4*z^2 - 322*x^3*y^3 - 58*x^3*y^2*z - 58*x^3*y*z^2 - 322*x^3*z^3 - 207*x^2*y^4 - 58*x^2*y^3*z + 708*x^2*y^2*z^2 - 58*x^2*y*z^3 - 207*x^2*z^4 + 190*x*y^5 + 58*x*y^4*z - 58*x*y^3*z^2 - 58*x*y^2*z^3 + 58*x*y*z^4 + 190*x*z^5 + 178*y^6 + 190*y^5*z - 207*y^4*z^2 - 322*y^3*z^3 - 207*y^2*z^4 + 190*y*z^5 + 178*z^6) := by
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
  have hn : 0 ≤ (178*x^6 + 190*x^5*y + 190*x^5*z - 207*x^4*y^2 + 58*x^4*y*z - 207*x^4*z^2 - 322*x^3*y^3 - 58*x^3*y^2*z - 58*x^3*y*z^2 - 322*x^3*z^3 - 207*x^2*y^4 - 58*x^2*y^3*z + 708*x^2*y^2*z^2 - 58*x^2*y*z^3 - 207*x^2*z^4 + 190*x*y^5 + 58*x*y^4*z - 58*x*y^3*z^2 - 58*x*y^2*z^3 + 58*x*y*z^4 + 190*x*z^5 + 178*y^6 + 190*y^5*z - 207*y^4*z^2 - 322*y^3*z^3 - 207*y^2*z^4 + 190*y*z^5 + 178*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x^2 / (y + z)^2 + y^2 / (z + x)^2 + z^2 / (x + y)^2) ≥ 1 / 225 * (47 * x^2 - 22 * x * y - 22 * x * z + 47 * y^2 - 22 * y * z + 47 * z^2) * (x^2 + y^2 + z^2 + 3 * x * y + 3 * y * z + 3 * x * z)^2 / ((y + z)^2 * (z + x)^2 * (x + y)^2)) := @solution
#print axioms solution
