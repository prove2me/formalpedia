-- Prove2me | solution 1 for WorkbookSource.base_57125
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:51:19.695167+00:00
-- url     : https://prove2.me/submissions/f2cc4ba5-f11c-4a39-a287-ebb4916c3f19

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) + y / (z + x)) * (y / (z + x) + z / (x + y)) * (z / (x + y) + x / (y + z)) ≥ (x / (x + y) + y / (z + x)) * (y / (y + z) + z / (x + y)) * (z / (z + x) + x / (y + z))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*z - x^4*y*z + x^4*z^2 + x^2*y^4 - 3*x^2*y^2*z^2 + x*y^5 - x*y^4*z - x*y*z^4 + y^2*z^4 + y*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * x^4 * (y - x)^2 + (8 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (8 : ℝ) * x^4 * (z - y)^2 + (22 : ℝ) * x^3 * (y - x)^3 + (42 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (40 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (10 : ℝ) * x^3 * (z - y)^3 + (23 : ℝ) * x^2 * (y - x)^4 + (64 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (75 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (34 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (5 : ℝ) * x^2 * (z - y)^4 + (11 : ℝ) * x^1 * (y - x)^5 + (40 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (58 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (38 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (11 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (1 : ℝ) * x^1 * (z - y)^5 + (2 : ℝ) * (y - x)^6 + (9 : ℝ) * (y - x)^5 * (z - y)^1 + (16 : ℝ) * (y - x)^4 * (z - y)^2 + (14 : ℝ) * (y - x)^3 * (z - y)^3 + (6 : ℝ) * (y - x)^2 * (z - y)^4 + (1 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (x^5*z - x^4*y*z + x^4*z^2 + x^2*y^4 - 3*x^2*y^2*z^2 + x*y^5 - x*y^4*z - x*y*z^4 + y^2*z^4 + y*z^5) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * x^4 * (z - x)^2 + (8 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (8 : ℝ) * x^4 * (y - z)^2 + (22 : ℝ) * x^3 * (z - x)^3 + (24 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (22 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (10 : ℝ) * x^3 * (y - z)^3 + (23 : ℝ) * x^2 * (z - x)^4 + (28 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (21 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (16 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (5 : ℝ) * x^2 * (y - z)^4 + (11 : ℝ) * x^1 * (z - x)^5 + (15 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (8 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (6 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (4 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (1 : ℝ) * x^1 * (y - z)^5 + (2 : ℝ) * (z - x)^6 + (3 : ℝ) * (z - x)^5 * (y - z)^1 + (1 : ℝ) * (z - x)^4 * (y - z)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*z - x^4*y*z + x^4*z^2 + x^2*y^4 - 3*x^2*y^2*z^2 + x*y^5 - x*y^4*z - x*y*z^4 + y^2*z^4 + y*z^5) := by
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
  have hn : 0 ≤ (x^5*z - x^4*y*z + x^4*z^2 + x^2*y^4 - 3*x^2*y^2*z^2 + x*y^5 - x*y^4*z - x*y*z^4 + y^2*z^4 + y*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x / (y + z) + y / (z + x)) * (y / (z + x) + z / (x + y)) * (z / (x + y) + x / (y + z)) ≥ (x / (x + y) + y / (z + x)) * (y / (y + z) + z / (x + y)) * (z / (z + x) + x / (y + z))) := @solution
#print axioms solution
