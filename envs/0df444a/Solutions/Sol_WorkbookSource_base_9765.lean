-- Prove2me | solution 1 for WorkbookSource.base_9765
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:46:41.437361+00:00
-- url     : https://prove2.me/submissions/56ae8831-de29-409e-83c0-ffe0a8e18abc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y * (y - x) / (x + y + x ^ 2) + z * (z - y) / (y + z + y ^ 2) + x * (x - z) / (z + x + z ^ 2)) ≥ 0  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^4*y^2 + x^4*y + x^4*z - x^3*y^2*z + x^3*y^2 - 2*x^3*y*z + x^3*y + x^3*z - x^2*y^2*z - x^2*y*z^3 - x^2*y*z^2 - 2*x^2*y*z + x^2*z^4 + x^2*z^3 + x*y^4 - x*y^3*z^2 - 2*x*y^3*z + x*y^3 - x*y^2*z^2 - 2*x*y^2*z - 2*x*y*z^3 - 2*x*y*z^2 + x*z^4 + x*z^3 + y^4*z^2 + y^4*z + y^3*z^2 + y^3*z + y*z^4 + y*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * x^4 * (y - x)^2 + (3 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (3 : ℝ) * x^4 * (z - y)^2 + (9 : ℝ) * x^3 * (y - x)^3 + (10 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (8 : ℝ) * x^3 * (y - x)^2 + (7 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (8 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (3 : ℝ) * x^3 * (z - y)^3 + (8 : ℝ) * x^3 * (z - y)^2 + (10 : ℝ) * x^2 * (y - x)^4 + (13 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (17 : ℝ) * x^2 * (y - x)^3 + (6 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (24 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (4 : ℝ) * x^2 * (y - x)^2 + (3 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (21 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (4 : ℝ) * x^2 * (y - x)^1 * (z - y)^1 + (1 : ℝ) * x^2 * (z - y)^4 + (7 : ℝ) * x^2 * (z - y)^3 + (4 : ℝ) * x^2 * (z - y)^2 + (5 : ℝ) * x^1 * (y - x)^5 + (8 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (12 : ℝ) * x^1 * (y - x)^4 + (3 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (22 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (6 : ℝ) * x^1 * (y - x)^3 + (20 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (9 : ℝ) * x^1 * (y - x)^2 * (z - y)^1 + (10 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (7 : ℝ) * x^1 * (y - x)^1 * (z - y)^2 + (2 : ℝ) * x^1 * (z - y)^4 + (2 : ℝ) * x^1 * (z - y)^3 + (1 : ℝ) * (y - x)^6 + (2 : ℝ) * (y - x)^5 * (z - y)^1 + (3 : ℝ) * (y - x)^5 + (1 : ℝ) * (y - x)^4 * (z - y)^2 + (7 : ℝ) * (y - x)^4 * (z - y)^1 + (2 : ℝ) * (y - x)^4 + (7 : ℝ) * (y - x)^3 * (z - y)^2 + (4 : ℝ) * (y - x)^3 * (z - y)^1 + (4 : ℝ) * (y - x)^2 * (z - y)^3 + (3 : ℝ) * (y - x)^2 * (z - y)^2 + (1 : ℝ) * (y - x)^1 * (z - y)^4 + (1 : ℝ) * (y - x)^1 * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (x^4*y^2 + x^4*y + x^4*z - x^3*y^2*z + x^3*y^2 - 2*x^3*y*z + x^3*y + x^3*z - x^2*y^2*z - x^2*y*z^3 - x^2*y*z^2 - 2*x^2*y*z + x^2*z^4 + x^2*z^3 + x*y^4 - x*y^3*z^2 - 2*x*y^3*z + x*y^3 - x*y^2*z^2 - 2*x*y^2*z - 2*x*y*z^3 - 2*x*y*z^2 + x*z^4 + x*z^3 + y^4*z^2 + y^4*z + y^3*z^2 + y^3*z + y*z^4 + y*z^3) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * x^4 * (z - x)^2 + (3 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (3 : ℝ) * x^4 * (y - z)^2 + (9 : ℝ) * x^3 * (z - x)^3 + (17 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (8 : ℝ) * x^3 * (z - x)^2 + (14 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (8 : ℝ) * x^3 * (z - x)^1 * (y - z)^1 + (3 : ℝ) * x^3 * (y - z)^3 + (8 : ℝ) * x^3 * (y - z)^2 + (10 : ℝ) * x^2 * (z - x)^4 + (27 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (17 : ℝ) * x^2 * (z - x)^3 + (27 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (27 : ℝ) * x^2 * (z - x)^2 * (y - z)^1 + (4 : ℝ) * x^2 * (z - x)^2 + (10 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (24 : ℝ) * x^2 * (z - x)^1 * (y - z)^2 + (4 : ℝ) * x^2 * (z - x)^1 * (y - z)^1 + (1 : ℝ) * x^2 * (y - z)^4 + (7 : ℝ) * x^2 * (y - z)^3 + (4 : ℝ) * x^2 * (y - z)^2 + (5 : ℝ) * x^1 * (z - x)^5 + (17 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (12 : ℝ) * x^1 * (z - x)^4 + (21 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (26 : ℝ) * x^1 * (z - x)^3 * (y - z)^1 + (6 : ℝ) * x^1 * (z - x)^3 + (11 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (26 : ℝ) * x^1 * (z - x)^2 * (y - z)^2 + (9 : ℝ) * x^1 * (z - x)^2 * (y - z)^1 + (2 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (12 : ℝ) * x^1 * (z - x)^1 * (y - z)^3 + (7 : ℝ) * x^1 * (z - x)^1 * (y - z)^2 + (2 : ℝ) * x^1 * (y - z)^4 + (2 : ℝ) * x^1 * (y - z)^3 + (1 : ℝ) * (z - x)^6 + (4 : ℝ) * (z - x)^5 * (y - z)^1 + (3 : ℝ) * (z - x)^5 + (6 : ℝ) * (z - x)^4 * (y - z)^2 + (8 : ℝ) * (z - x)^4 * (y - z)^1 + (2 : ℝ) * (z - x)^4 + (4 : ℝ) * (z - x)^3 * (y - z)^3 + (9 : ℝ) * (z - x)^3 * (y - z)^2 + (4 : ℝ) * (z - x)^3 * (y - z)^1 + (1 : ℝ) * (z - x)^2 * (y - z)^4 + (5 : ℝ) * (z - x)^2 * (y - z)^3 + (3 : ℝ) * (z - x)^2 * (y - z)^2 + (1 : ℝ) * (z - x)^1 * (y - z)^4 + (1 : ℝ) * (z - x)^1 * (y - z)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^4*y^2 + x^4*y + x^4*z - x^3*y^2*z + x^3*y^2 - 2*x^3*y*z + x^3*y + x^3*z - x^2*y^2*z - x^2*y*z^3 - x^2*y*z^2 - 2*x^2*y*z + x^2*z^4 + x^2*z^3 + x*y^4 - x*y^3*z^2 - 2*x*y^3*z + x*y^3 - x*y^2*z^2 - 2*x*y^2*z - 2*x*y*z^3 - 2*x*y*z^2 + x*z^4 + x*z^3 + y^4*z^2 + y^4*z + y^3*z^2 + y^3*z + y*z^4 + y*z^3) := by
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
  have hn : 0 ≤ (x^4*y^2 + x^4*y + x^4*z - x^3*y^2*z + x^3*y^2 - 2*x^3*y*z + x^3*y + x^3*z - x^2*y^2*z - x^2*y*z^3 - x^2*y*z^2 - 2*x^2*y*z + x^2*z^4 + x^2*z^3 + x*y^4 - x*y^3*z^2 - 2*x*y^3*z + x*y^3 - x*y^2*z^2 - 2*x*y^2*z - 2*x*y*z^3 - 2*x*y*z^2 + x*z^4 + x*z^3 + y^4*z^2 + y^4*z + y^3*z^2 + y^3*z + y*z^4 + y*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (y * (y - x) / (x + y + x ^ 2) + z * (z - y) / (y + z + y ^ 2) + x * (x - z) / (z + x + z ^ 2)) ≥ 0) := @solution
#print axioms solution
