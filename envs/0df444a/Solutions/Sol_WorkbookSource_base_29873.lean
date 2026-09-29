-- Prove2me | solution 1 for WorkbookSource.base_29873
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:34.727892+00:00
-- url     : https://prove2.me/submissions/56395bb5-6e2d-48af-89cc-85eb79423369

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^3 + y^3 + z^3)^2 ≥ 3 * (x^4 * z^2 + y^4 * x^2 + z^4 * y^2)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6 - 3*x^4*z^2 + 2*x^3*y^3 + 2*x^3*z^3 - 3*x^2*y^4 + y^6 + 2*y^3*z^3 - 3*y^2*z^4 + z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * x^4 * (y - x)^2 + (6 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (6 : ℝ) * x^4 * (z - y)^2 + (12 : ℝ) * x^3 * (y - x)^3 + (6 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (18 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (12 : ℝ) * x^3 * (z - y)^3 + (12 : ℝ) * x^2 * (y - x)^4 + (18 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (30 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (12 : ℝ) * x^2 * (z - y)^4 + (6 : ℝ) * x^1 * (y - x)^5 + (12 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (30 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (24 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (6 : ℝ) * x^1 * (z - y)^5 + (1 : ℝ) * (y - x)^6 + (3 : ℝ) * (y - x)^4 * (z - y)^2 + (10 : ℝ) * (y - x)^3 * (z - y)^3 + (12 : ℝ) * (y - x)^2 * (z - y)^4 + (6 : ℝ) * (y - x)^1 * (z - y)^5 + (1 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (x^6 - 3*x^4*z^2 + 2*x^3*y^3 + 2*x^3*z^3 - 3*x^2*y^4 + y^6 + 2*y^3*z^3 - 3*y^2*z^4 + z^6) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * x^4 * (z - x)^2 + (6 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (6 : ℝ) * x^4 * (y - z)^2 + (12 : ℝ) * x^3 * (z - x)^3 + (30 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (42 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (12 : ℝ) * x^3 * (y - z)^3 + (12 : ℝ) * x^2 * (z - x)^4 + (48 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (90 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (54 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (12 : ℝ) * x^2 * (y - z)^4 + (6 : ℝ) * x^1 * (z - x)^5 + (30 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (72 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (66 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (30 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (6 : ℝ) * x^1 * (y - z)^5 + (1 : ℝ) * (z - x)^6 + (6 : ℝ) * (z - x)^5 * (y - z)^1 + (18 : ℝ) * (z - x)^4 * (y - z)^2 + (22 : ℝ) * (z - x)^3 * (y - z)^3 + (15 : ℝ) * (z - x)^2 * (y - z)^4 + (6 : ℝ) * (z - x)^1 * (y - z)^5 + (1 : ℝ) * (y - z)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6 - 3*x^4*z^2 + 2*x^3*y^3 + 2*x^3*z^3 - 3*x^2*y^4 + y^6 + 2*y^3*z^3 - 3*y^2*z^4 + z^6) := by
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
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x^3 + y^3 + z^3)^2 ≥ 3 * (x^4 * z^2 + y^4 * x^2 + z^4 * y^2)) := @solution
#print axioms solution
