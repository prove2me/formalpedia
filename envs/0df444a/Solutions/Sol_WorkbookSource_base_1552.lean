-- Prove2me | solution 1 for WorkbookSource.base_1552
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:42.235596+00:00
-- url     : https://prove2.me/submissions/40715d27-0573-485a-9857-a5db9d76a232

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y ^ 2 + z ^ 2) / x + (z ^ 2 + x ^ 2) / y + (x ^ 2 + y ^ 2) / z ≥ 2 * (x + y + z)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^3*y + x^3*z - 2*x^2*y*z + x*y^3 - 2*x*y^2*z - 2*x*y*z^2 + x*z^3 + y^3*z + y*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * x^2 * (y - x)^2 + (4 : ℝ) * x^2 * (y - x)^1 * (z - y)^1 + (4 : ℝ) * x^2 * (z - y)^2 + (6 : ℝ) * x^1 * (y - x)^3 + (9 : ℝ) * x^1 * (y - x)^2 * (z - y)^1 + (7 : ℝ) * x^1 * (y - x)^1 * (z - y)^2 + (2 : ℝ) * x^1 * (z - y)^3 + (2 : ℝ) * (y - x)^4 + (4 : ℝ) * (y - x)^3 * (z - y)^1 + (3 : ℝ) * (y - x)^2 * (z - y)^2 + (1 : ℝ) * (y - x)^1 * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^3*y + x^3*z - 2*x^2*y*z + x*y^3 - 2*x*y^2*z - 2*x*y*z^2 + x*z^3 + y^3*z + y*z^3) := by
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
  have hn : 0 ≤ (x^3*y + x^3*z - 2*x^2*y*z + x*y^3 - 2*x*y^2*z - 2*x*y*z^2 + x*z^3 + y^3*z + y*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (y ^ 2 + z ^ 2) / x + (z ^ 2 + x ^ 2) / y + (x ^ 2 + y ^ 2) / z ≥ 2 * (x + y + z)) := @solution
#print axioms solution
