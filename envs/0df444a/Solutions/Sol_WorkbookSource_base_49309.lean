-- Prove2me | solution 1 for WorkbookSource.base_49309
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:26.258769+00:00
-- url     : https://prove2.me/submissions/0c79e047-78b3-4511-8332-de45a63b915e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x^4 + y^4 + z^4)^2 ≥ 3 * x * y * z * (x^5 + y^5 + z^5)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^8 - 3*x^6*y*z + 2*x^4*y^4 + 2*x^4*z^4 - 3*x*y^6*z - 3*x*y*z^6 + y^8 + 2*y^4*z^4 + z^8) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (7 : ℝ) * x^6 * (y - x)^2 + (7 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (7 : ℝ) * x^6 * (z - y)^2 + (30 : ℝ) * x^5 * (y - x)^3 + (45 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (39 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (12 : ℝ) * x^5 * (z - y)^3 + (74 : ℝ) * x^4 * (y - x)^4 + (148 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (162 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (88 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (29 : ℝ) * x^4 * (z - y)^4 + (98 : ℝ) * x^3 * (y - x)^5 + (245 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (350 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (280 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (153 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (38 : ℝ) * x^3 * (z - y)^5 + (70 : ℝ) * x^2 * (y - x)^6 + (210 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (375 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (400 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (297 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (132 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (25 : ℝ) * x^2 * (z - y)^6 + (26 : ℝ) * x^1 * (y - x)^7 + (91 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (195 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (260 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (243 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (150 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (53 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (8 : ℝ) * x^1 * (z - y)^7 + (4 : ℝ) * (y - x)^8 + (16 : ℝ) * (y - x)^7 * (z - y)^1 + (40 : ℝ) * (y - x)^6 * (z - y)^2 + (64 : ℝ) * (y - x)^5 * (z - y)^3 + (72 : ℝ) * (y - x)^4 * (z - y)^4 + (56 : ℝ) * (y - x)^3 * (z - y)^5 + (28 : ℝ) * (y - x)^2 * (z - y)^6 + (8 : ℝ) * (y - x)^1 * (z - y)^7 + (1 : ℝ) * (z - y)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^8 - 3*x^6*y*z + 2*x^4*y^4 + 2*x^4*z^4 - 3*x*y^6*z - 3*x*y*z^6 + y^8 + 2*y^4*z^4 + z^8) := by
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
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), (x^4 + y^4 + z^4)^2 ≥ 3 * x * y * z * (x^5 + y^5 + z^5)) := @solution
#print axioms solution
