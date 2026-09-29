-- Prove2me | solution 1 for WorkbookSource.base_55925
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:32.313793+00:00
-- url     : https://prove2.me/submissions/5190468c-c4a6-4a35-bce5-484a26970cd1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (h : x + y + z = 2) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 - 2 * x * y * z ≤ 1  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^4/16 + x^3*y/4 + x^3*z/4 - 5*x^2*y^2/8 + 7*x^2*y*z/4 - 5*x^2*z^2/8 + x*y^3/4 + 7*x*y^2*z/4 + 7*x*y*z^2/4 + x*z^3/4 + y^4/16 + y^3*z/4 - 5*y^2*z^2/8 + y*z^3/4 + z^4/16) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (81/16 : ℝ) * x^4 + (27/2 : ℝ) * x^3 * (y - x)^1 + (27/4 : ℝ) * x^3 * (z - y)^1 + (25/2 : ℝ) * x^2 * (y - x)^2 + (25/2 : ℝ) * x^2 * (y - x)^1 * (z - y)^1 + (19/8 : ℝ) * x^2 * (z - y)^2 + (4 : ℝ) * x^1 * (y - x)^3 + (6 : ℝ) * x^1 * (y - x)^2 * (z - y)^1 + (7/2 : ℝ) * x^1 * (y - x)^1 * (z - y)^2 + (3/4 : ℝ) * x^1 * (z - y)^3 + (1/2 : ℝ) * (y - x)^2 * (z - y)^2 + (1/2 : ℝ) * (y - x)^1 * (z - y)^3 + (1/16 : ℝ) * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^4/16 + x^3*y/4 + x^3*z/4 - 5*x^2*y^2/8 + 7*x^2*y*z/4 - 5*x^2*z^2/8 + x*y^3/4 + 7*x*y^2*z/4 + 7*x*y*z^2/4 + x*z^3/4 + y^4/16 + y^3*z/4 - 5*y^2*z^2/8 + y*z^3/4 + z^4/16) := by
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
  have he : (-x^2*y^2 - x^2*z^2 + 2*x*y*z - y^2*z^2 + 1) = (x^4/16 + x^3*y/4 + x^3*z/4 - 5*x^2*y^2/8 + 7*x^2*y*z/4 - 5*x^2*z^2/8 + x*y^3/4 + 7*x*y^2*z/4 + 7*x*y*z^2/4 + x*z^3/4 + y^4/16 + y^3*z/4 - 5*y^2*z^2/8 + y*z^3/4 + z^4/16) := by
    linear_combination (-x^3/16 - 3*x^2*y/16 - 3*x^2*z/16 - x^2/8 - 3*x*y^2/16 - 11*x*y*z/8 - x*y/4 - 3*x*z^2/16 - x*z/4 - x/4 - y^3/16 - 3*y^2*z/16 - y^2/8 - 3*y*z^2/16 - y*z/4 - y/4 - z^3/16 - z^2/8 - z/4 - 1/2) * h
  nlinarith only [hp, he]
example : (∀ (x y z : ℝ) (h : x + y + z = 2) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0), x^2 * y^2 + y^2 * z^2 + z^2 * x^2 - 2 * x * y * z ≤ 1) := @solution
#print axioms solution
