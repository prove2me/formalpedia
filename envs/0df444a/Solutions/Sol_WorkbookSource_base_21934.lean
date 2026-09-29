-- Prove2me | solution 1 for WorkbookSource.base_21934
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:51:01.300695+00:00
-- url     : https://prove2.me/submissions/cffdceb2-2d1d-4ee4-87ad-71f857a3875c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (x + y) + 3 * (y / (z + x))) * (y / (y + z) + 3 * (z / (x + y))) * (z / (z + x) + 3 * (x / (y + z))) ≥ 8  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (3*x^5*y + 4*x^4*y^2 - x^4*y*z + x^4*z^2 + 2*x^3*y^3 - 5*x^3*y^2*z + x^3*y*z^2 + 2*x^3*z^3 + x^2*y^4 + x^2*y^3*z - 15*x^2*y^2*z^2 - 5*x^2*y*z^3 + 4*x^2*z^4 - x*y^4*z - 5*x*y^3*z^2 + x*y^2*z^3 - x*y*z^4 + 3*x*z^5 + 3*y^5*z + 4*y^4*z^2 + 2*y^3*z^3 + y^2*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * x^4 * (y - x)^2 + (40 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (40 : ℝ) * x^4 * (z - y)^2 + (114 : ℝ) * x^3 * (y - x)^3 + (147 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (125 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (46 : ℝ) * x^3 * (z - y)^3 + (121 : ℝ) * x^2 * (y - x)^4 + (194 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (156 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (83 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (19 : ℝ) * x^2 * (z - y)^4 + (57 : ℝ) * x^1 * (y - x)^5 + (108 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (86 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (45 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (16 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (3 : ℝ) * x^1 * (z - y)^5 + (10 : ℝ) * (y - x)^6 + (21 : ℝ) * (y - x)^5 * (z - y)^1 + (16 : ℝ) * (y - x)^4 * (z - y)^2 + (6 : ℝ) * (y - x)^3 * (z - y)^3 + (1 : ℝ) * (y - x)^2 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (3*x^5*y + 4*x^4*y^2 - x^4*y*z + x^4*z^2 + 2*x^3*y^3 - 5*x^3*y^2*z + x^3*y*z^2 + 2*x^3*z^3 + x^2*y^4 + x^2*y^3*z - 15*x^2*y^2*z^2 - 5*x^2*y*z^3 + 4*x^2*z^4 - x*y^4*z - 5*x*y^3*z^2 + x*y^2*z^3 - x*y*z^4 + 3*x*z^5 + 3*y^5*z + 4*y^4*z^2 + 2*y^3*z^3 + y^2*z^4) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * x^4 * (z - x)^2 + (40 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (40 : ℝ) * x^4 * (y - z)^2 + (114 : ℝ) * x^3 * (z - x)^3 + (195 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (173 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (46 : ℝ) * x^3 * (y - z)^3 + (121 : ℝ) * x^2 * (z - x)^4 + (290 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (300 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (131 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (19 : ℝ) * x^2 * (y - z)^4 + (57 : ℝ) * x^1 * (z - x)^5 + (177 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (224 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (135 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (37 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (3 : ℝ) * x^1 * (y - z)^5 + (10 : ℝ) * (z - x)^6 + (39 : ℝ) * (z - x)^5 * (y - z)^1 + (61 : ℝ) * (z - x)^4 * (y - z)^2 + (48 : ℝ) * (z - x)^3 * (y - z)^3 + (19 : ℝ) * (z - x)^2 * (y - z)^4 + (3 : ℝ) * (z - x)^1 * (y - z)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*x^5*y + 4*x^4*y^2 - x^4*y*z + x^4*z^2 + 2*x^3*y^3 - 5*x^3*y^2*z + x^3*y*z^2 + 2*x^3*z^3 + x^2*y^4 + x^2*y^3*z - 15*x^2*y^2*z^2 - 5*x^2*y*z^3 + 4*x^2*z^4 - x*y^4*z - 5*x*y^3*z^2 + x*y^2*z^3 - x*y*z^4 + 3*x*z^5 + 3*y^5*z + 4*y^4*z^2 + 2*y^3*z^3 + y^2*z^4) := by
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
  have hn : 0 ≤ (3*x^5*y + 4*x^4*y^2 - x^4*y*z + x^4*z^2 + 2*x^3*y^3 - 5*x^3*y^2*z + x^3*y*z^2 + 2*x^3*z^3 + x^2*y^4 + x^2*y^3*z - 15*x^2*y^2*z^2 - 5*x^2*y*z^3 + 4*x^2*z^4 - x*y^4*z - 5*x*y^3*z^2 + x*y^2*z^3 - x*y*z^4 + 3*x*z^5 + 3*y^5*z + 4*y^4*z^2 + 2*y^3*z^3 + y^2*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x / (x + y) + 3 * (y / (z + x))) * (y / (y + z) + 3 * (z / (x + y))) * (z / (z + x) + 3 * (x / (y + z))) ≥ 8) := @solution
#print axioms solution
