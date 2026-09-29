-- Prove2me | solution 1 for WorkbookSource.base_36028
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:32.619036+00:00
-- url     : https://prove2.me/submissions/1b0abdb0-27aa-49fd-b9e6-4344d1ce2a7e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x^3 * y + y^3 * z + z^3 * x) * (x^2 + y^2 + z^2) ≥ (x * y + y * z + z * x) * (y^2 * z^2 + z^2 * x^2 + x^2 * y^2)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*y - x^3*y^2*z - x^2*y*z^3 - x*y^3*z^2 + x*z^5 + y^5*z) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * x^4 * (y - x)^2 + (6 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (6 : ℝ) * x^4 * (z - y)^2 + (15 : ℝ) * x^3 * (y - x)^3 + (18 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (21 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (9 : ℝ) * x^3 * (z - y)^3 + (14 : ℝ) * x^2 * (y - x)^4 + (19 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (24 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (19 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (5 : ℝ) * x^2 * (z - y)^4 + (6 : ℝ) * x^1 * (y - x)^5 + (8 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (9 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (10 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (5 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (1 : ℝ) * x^1 * (z - y)^5 + (1 : ℝ) * (y - x)^6 + (1 : ℝ) * (y - x)^5 * (z - y)^1 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (x^5*y - x^3*y^2*z - x^2*y*z^3 - x*y^3*z^2 + x*z^5 + y^5*z) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * x^4 * (z - x)^2 + (6 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (6 : ℝ) * x^4 * (y - z)^2 + (15 : ℝ) * x^3 * (z - x)^3 + (27 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (30 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (9 : ℝ) * x^3 * (y - z)^3 + (14 : ℝ) * x^2 * (z - x)^4 + (37 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (51 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (28 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (5 : ℝ) * x^2 * (y - z)^4 + (6 : ℝ) * x^1 * (z - x)^5 + (22 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (37 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (29 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (10 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (1 : ℝ) * x^1 * (y - z)^5 + (1 : ℝ) * (z - x)^6 + (5 : ℝ) * (z - x)^5 * (y - z)^1 + (10 : ℝ) * (z - x)^4 * (y - z)^2 + (10 : ℝ) * (z - x)^3 * (y - z)^3 + (5 : ℝ) * (z - x)^2 * (y - z)^4 + (1 : ℝ) * (z - x)^1 * (y - z)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*y - x^3*y^2*z - x^2*y*z^3 - x*y^3*z^2 + x*z^5 + y^5*z) := by
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
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0), (x^3 * y + y^3 * z + z^3 * x) * (x^2 + y^2 + z^2) ≥ (x * y + y * z + z * x) * (y^2 * z^2 + z^2 * x^2 + x^2 * y^2)) := @solution
#print axioms solution
