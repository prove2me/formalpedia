-- Prove2me | solution 1 for WorkbookSource.plus_28880
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:34:40.241174+00:00
-- url     : https://prove2.me/submissions/2ec7e54b-33c6-4c36-a4fc-9587a78a3771

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    (x * y^2 + y * z^2 + z * x^2) * (x^2 * y + y^2 * z + z^2 * x) * (x * y + y * z + z * x) ≥ 3 * (x + y + z)^2 * (x * y * z)^2   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*y^2*z + x^5*y*z^2 + x^4*y^4 + x^4*y^3*z - 2*x^4*y^2*z^2 + x^4*y*z^3 + x^4*z^4 + x^3*y^4*z - 3*x^3*y^3*z^2 - 3*x^3*y^2*z^3 + x^3*y*z^4 + x^2*y^5*z - 2*x^2*y^4*z^2 - 3*x^2*y^3*z^3 - 2*x^2*y^2*z^4 + x^2*y*z^5 + x*y^5*z^2 + x*y^4*z^3 + x*y^3*z^4 + x*y^2*z^5 + y^4*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (15 : ℝ) * x^6 * (y - x)^2 + (15 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (15 : ℝ) * x^6 * (z - y)^2 + (66 : ℝ) * x^5 * (y - x)^3 + (99 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (81 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (24 : ℝ) * x^5 * (z - y)^3 + (117 : ℝ) * x^4 * (y - x)^4 + (234 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (201 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (84 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (12 : ℝ) * x^4 * (z - y)^4 + (106 : ℝ) * x^3 * (y - x)^5 + (265 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (262 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (128 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (29 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (2 : ℝ) * x^3 * (z - y)^5 + (51 : ℝ) * x^2 * (y - x)^6 + (153 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (177 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (99 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (27 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (3 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (12 : ℝ) * x^1 * (y - x)^7 + (42 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (56 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (35 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (10 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (1 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (1 : ℝ) * (y - x)^8 + (4 : ℝ) * (y - x)^7 * (z - y)^1 + (6 : ℝ) * (y - x)^6 * (z - y)^2 + (4 : ℝ) * (y - x)^5 * (z - y)^3 + (1 : ℝ) * (y - x)^4 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*y^2*z + x^5*y*z^2 + x^4*y^4 + x^4*y^3*z - 2*x^4*y^2*z^2 + x^4*y*z^3 + x^4*z^4 + x^3*y^4*z - 3*x^3*y^3*z^2 - 3*x^3*y^2*z^3 + x^3*y*z^4 + x^2*y^5*z - 2*x^2*y^4*z^2 - 3*x^2*y^3*z^3 - 2*x^2*y^2*z^4 + x^2*y*z^5 + x*y^5*z^2 + x*y^4*z^3 + x*y^3*z^4 + x*y^2*z^5 + y^4*z^4) := by
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
example : (∀ (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z), (x * y^2 + y * z^2 + z * x^2) * (x^2 * y + y^2 * z + z^2 * x) * (x * y + y * z + z * x) ≥ 3 * (x + y + z)^2 * (x * y * z)^2) := @solution
#print axioms solution
