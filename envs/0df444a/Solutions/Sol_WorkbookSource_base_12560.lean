-- Prove2me | solution 1 for WorkbookSource.base_12560
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:44:25.411148+00:00
-- url     : https://prove2.me/submissions/e9b83777-e788-4be9-9bf0-6f2cbf8ec731

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x) + 3 * x * y * z / (x ^ 3 + y ^ 3 + z ^ 3) ≥ 4  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (3*x^5 - 4*x^4*y - 4*x^4*z + 3*x^3*y^2 - 4*x^3*y*z + 3*x^3*z^2 + 3*x^2*y^3 + 3*x^2*y^2*z + 3*x^2*y*z^2 + 3*x^2*z^3 - 4*x*y^4 - 4*x*y^3*z + 3*x*y^2*z^2 - 4*x*y*z^3 - 4*x*z^4 + 3*y^5 - 4*y^4*z + 3*y^3*z^2 + 3*y^2*z^3 - 4*y*z^4 + 3*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (7 : ℝ) * x^1 * (y - x)^4 + (14 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (21 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (14 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (7 : ℝ) * x^1 * (z - y)^4 + (4 : ℝ) * (y - x)^5 + (10 : ℝ) * (y - x)^4 * (z - y)^1 + (18 : ℝ) * (y - x)^3 * (z - y)^2 + (17 : ℝ) * (y - x)^2 * (z - y)^3 + (11 : ℝ) * (y - x)^1 * (z - y)^4 + (3 : ℝ) * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*x^5 - 4*x^4*y - 4*x^4*z + 3*x^3*y^2 - 4*x^3*y*z + 3*x^3*z^2 + 3*x^2*y^3 + 3*x^2*y^2*z + 3*x^2*y*z^2 + 3*x^2*z^3 - 4*x*y^4 - 4*x*y^3*z + 3*x*y^2*z^2 - 4*x*y*z^3 - 4*x*z^4 + 3*y^5 - 4*y^4*z + 3*y^3*z^2 + 3*y^2*z^3 - 4*y*z^4 + 3*z^5) := by
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
  have hn : 0 ≤ ((x^2 - x*y - x*z + y^2 - y*z + z^2)*(3*x^3 - x^2*y - x^2*z - x*y^2 - 3*x*y*z - x*z^2 + 3*y^3 - y^2*z - y*z^2 + 3*z^3)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x) + 3 * x * y * z / (x ^ 3 + y ^ 3 + z ^ 3) ≥ 4) := @solution
#print axioms solution
