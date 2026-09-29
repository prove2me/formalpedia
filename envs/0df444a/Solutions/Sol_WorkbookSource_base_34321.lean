-- Prove2me | solution 1 for WorkbookSource.base_34321
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:08.216187+00:00
-- url     : https://prove2.me/submissions/bc8b8273-5114-490b-ae1a-588269025fff

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / 6) * ((x + y) / (y + z) + (y + z) / (z + x) + (z + x) / (x + y)) * ((x + y) / (z + x) + (y + z) / (x + y) + (z + x) / (y + z)) ≥ x / (y + z) + y / (z + x) + z / (x + y)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6 - x^5*y - x^5*z - x^4*y^2 + x^4*y*z - x^4*z^2 + 3*x^3*y^3 - x^3*y^2*z - x^3*y*z^2 + 3*x^3*z^3 - x^2*y^4 - x^2*y^3*z + 3*x^2*y^2*z^2 - x^2*y*z^3 - x^2*z^4 - x*y^5 + x*y^4*z - x*y^3*z^2 - x*y^2*z^3 + x*y*z^4 - x*z^5 + y^6 - y^5*z - y^4*z^2 + 3*y^3*z^3 - y^2*z^4 - y*z^5 + z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * x^2 * (y - x)^4 + (8 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (12 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (8 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (4 : ℝ) * x^2 * (z - y)^4 + (4 : ℝ) * x^1 * (y - x)^5 + (10 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (20 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (20 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (14 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (4 : ℝ) * x^1 * (z - y)^5 + (1 : ℝ) * (y - x)^6 + (3 : ℝ) * (y - x)^5 * (z - y)^1 + (7 : ℝ) * (y - x)^4 * (z - y)^2 + (9 : ℝ) * (y - x)^3 * (z - y)^3 + (9 : ℝ) * (y - x)^2 * (z - y)^4 + (5 : ℝ) * (y - x)^1 * (z - y)^5 + (1 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6 - x^5*y - x^5*z - x^4*y^2 + x^4*y*z - x^4*z^2 + 3*x^3*y^3 - x^3*y^2*z - x^3*y*z^2 + 3*x^3*z^3 - x^2*y^4 - x^2*y^3*z + 3*x^2*y^2*z^2 - x^2*y*z^3 - x^2*z^4 - x*y^5 + x*y^4*z - x*y^3*z^2 - x*y^2*z^3 + x*y*z^4 - x*z^5 + y^6 - y^5*z - y^4*z^2 + 3*y^3*z^3 - y^2*z^4 - y*z^5 + z^6) := by
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
  have hn : 0 ≤ ((x^3 - x^2*y - x*z^2 + y^3 - y^2*z + z^3)*(x^3 - x^2*z - x*y^2 + y^3 - y*z^2 + z^3)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (1 / 6) * ((x + y) / (y + z) + (y + z) / (z + x) + (z + x) / (x + y)) * ((x + y) / (z + x) + (y + z) / (x + y) + (z + x) / (y + z)) ≥ x / (y + z) + y / (z + x) + z / (x + y)) := @solution
#print axioms solution
