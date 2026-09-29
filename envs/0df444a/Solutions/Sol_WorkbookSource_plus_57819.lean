-- Prove2me | solution 1 for WorkbookSource.plus_57819
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:45:10.205913+00:00
-- url     : https://prove2.me/submissions/7f13b336-e5b2-49b2-a873-bb2ca6d8a973

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hx1 : x + y + z = 3) : 1 / (x + y * z) + 1 / (y + z * x) + 1 / (z + x * y) ≤ 9 / (2 * (x * y + x * z + y * z))   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^4*y^2/9 + 14*x^4*y*z/9 + x^4*z^2/9 + 2*x^3*y^3/9 - 10*x^3*y^2*z/9 - 10*x^3*y*z^2/9 + 2*x^3*z^3/9 + x^2*y^4/9 - 10*x^2*y^3*z/9 + 2*x^2*y^2*z^2/3 - 10*x^2*y*z^3/9 + x^2*z^4/9 + 14*x*y^4*z/9 - 10*x*y^3*z^2/9 - 10*x*y^2*z^3/9 + 14*x*y*z^4/9 + y^4*z^2/9 + 2*y^3*z^3/9 + y^2*z^4/9) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * x^4 * (y - x)^2 + (4 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (4 : ℝ) * x^4 * (z - y)^2 + (32/3 : ℝ) * x^3 * (y - x)^3 + (16 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (16 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (16/3 : ℝ) * x^3 * (z - y)^3 + (88/9 : ℝ) * x^2 * (y - x)^4 + (176/9 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (64/3 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (104/9 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (16/9 : ℝ) * x^2 * (z - y)^4 + (32/9 : ℝ) * x^1 * (y - x)^5 + (80/9 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (32/3 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (64/9 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (16/9 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (4/9 : ℝ) * (y - x)^6 + (4/3 : ℝ) * (y - x)^5 * (z - y)^1 + (13/9 : ℝ) * (y - x)^4 * (z - y)^2 + (2/3 : ℝ) * (y - x)^3 * (z - y)^3 + (1/9 : ℝ) * (y - x)^2 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^4*y^2/9 + 14*x^4*y*z/9 + x^4*z^2/9 + 2*x^3*y^3/9 - 10*x^3*y^2*z/9 - 10*x^3*y*z^2/9 + 2*x^3*z^3/9 + x^2*y^4/9 - 10*x^2*y^3*z/9 + 2*x^2*y^2*z^2/3 - 10*x^2*y*z^3/9 + x^2*z^4/9 + 14*x*y^4*z/9 - 10*x*y^3*z^2/9 - 10*x*y^2*z^3/9 + 14*x*y*z^4/9 + y^4*z^2/9 + 2*y^3*z^3/9 + y^2*z^4/9) := by
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
  have he : (-2*x^3*y^2*z - 2*x^3*y^2 - 2*x^3*y*z^2 + 5*x^3*y*z - 2*x^3*z^2 - 2*x^2*y^3*z - 2*x^2*y^3 + 3*x^2*y^2*z^2 - 4*x^2*y^2*z + 7*x^2*y^2 - 2*x^2*y*z^3 - 4*x^2*y*z^2 - 4*x^2*y*z - 2*x^2*z^3 + 7*x^2*z^2 - 2*x*y^3*z^2 + 5*x*y^3*z - 2*x*y^2*z^3 - 4*x*y^2*z^2 - 4*x*y^2*z + 5*x*y*z^3 - 4*x*y*z^2 + 9*x*y*z - 2*y^3*z^2 - 2*y^2*z^3 + 7*y^2*z^2) = (x^4*y^2/9 + 14*x^4*y*z/9 + x^4*z^2/9 + 2*x^3*y^3/9 - 10*x^3*y^2*z/9 - 10*x^3*y*z^2/9 + 2*x^3*z^3/9 + x^2*y^4/9 - 10*x^2*y^3*z/9 + 2*x^2*y^2*z^2/3 - 10*x^2*y*z^3/9 + x^2*z^4/9 + 14*x*y^4*z/9 - 10*x*y^3*z^2/9 - 10*x*y^2*z^3/9 + 14*x*y*z^4/9 + y^4*z^2/9 + 2*y^3*z^3/9 + y^2*z^4/9) := by
    linear_combination (-x^3*y^2/9 - 14*x^3*y*z/9 - x^3*z^2/9 - x^2*y^3/9 + 7*x^2*y^2*z/9 - 7*x^2*y^2/3 + 7*x^2*y*z^2/9 + x^2*y*z/3 - x^2*z^3/9 - 7*x^2*z^2/3 - 14*x*y^3*z/9 + 7*x*y^2*z^2/9 + x*y^2*z/3 - 14*x*y*z^3/9 + x*y*z^2/3 - 3*x*y*z - y^3*z^2/9 - y^2*z^3/9 - 7*y^2*z^2/3) * hx1
  have hn : 0 ≤ (-2*x^3*y^2*z - 2*x^3*y^2 - 2*x^3*y*z^2 + 5*x^3*y*z - 2*x^3*z^2 - 2*x^2*y^3*z - 2*x^2*y^3 + 3*x^2*y^2*z^2 - 4*x^2*y^2*z + 7*x^2*y^2 - 2*x^2*y*z^3 - 4*x^2*y*z^2 - 4*x^2*y*z - 2*x^2*z^3 + 7*x^2*z^2 - 2*x*y^3*z^2 + 5*x*y^3*z - 2*x*y^2*z^3 - 4*x*y^2*z^2 - 4*x*y^2*z + 5*x*y*z^3 - 4*x*y*z^2 + 9*x*y*z - 2*y^3*z^2 - 2*y^2*z^3 + 7*y^2*z^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hx1 : x + y + z = 3), 1 / (x + y * z) + 1 / (y + z * x) + 1 / (z + x * y) ≤ 9 / (2 * (x * y + x * z + y * z))) := @solution
#print axioms solution
