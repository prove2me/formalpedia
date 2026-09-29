-- Prove2me | solution 1 for WorkbookSource.base_3553
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:09:18.770362+00:00
-- url     : https://prove2.me/submissions/a9a9dea2-cae8-415d-9076-883d7409c1ca

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2*x + y + z)^2 / (2 * x^2 + (y + z)^2) + (2*y + z + x)^2 / (2 * y^2 + (z + x)^2) + (2*z + x + y)^2 / (2 * z^2 + (x + y)^2) ≤ 8  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (8*x^6 + 4*x^5*y + 4*x^5*z + x^4*y^2 + 10*x^4*y*z + x^4*z^2 + 10*x^3*y^3 - 26*x^3*y^2*z - 26*x^3*y*z^2 + 10*x^3*z^3 + x^2*y^4 - 26*x^2*y^3*z + 42*x^2*y^2*z^2 - 26*x^2*y*z^3 + x^2*z^4 + 4*x*y^5 + 10*x*y^4*z - 26*x*y^3*z^2 - 26*x*y^2*z^3 + 10*x*y*z^4 + 4*x*z^5 + 8*y^6 + 4*y^5*z + y^4*z^2 + 10*y^3*z^3 + y^2*z^4 + 4*y*z^5 + 8*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (168 : ℝ) * x^4 * (y - x)^2 + (168 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (168 : ℝ) * x^4 * (z - y)^2 + (416 : ℝ) * x^3 * (y - x)^3 + (624 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (720 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (256 : ℝ) * x^3 * (z - y)^3 + (412 : ℝ) * x^2 * (y - x)^4 + (824 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (1140 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (728 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (172 : ℝ) * x^2 * (z - y)^4 + (192 : ℝ) * x^1 * (y - x)^5 + (480 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (784 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (696 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (312 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (56 : ℝ) * x^1 * (z - y)^5 + (36 : ℝ) * (y - x)^6 + (108 : ℝ) * (y - x)^5 * (z - y)^1 + (197 : ℝ) * (y - x)^4 * (z - y)^2 + (214 : ℝ) * (y - x)^3 * (z - y)^3 + (141 : ℝ) * (y - x)^2 * (z - y)^4 + (52 : ℝ) * (y - x)^1 * (z - y)^5 + (8 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*x^6 + 4*x^5*y + 4*x^5*z + x^4*y^2 + 10*x^4*y*z + x^4*z^2 + 10*x^3*y^3 - 26*x^3*y^2*z - 26*x^3*y*z^2 + 10*x^3*z^3 + x^2*y^4 - 26*x^2*y^3*z + 42*x^2*y^2*z^2 - 26*x^2*y*z^3 + x^2*z^4 + 4*x*y^5 + 10*x*y^4*z - 26*x*y^3*z^2 - 26*x*y^2*z^3 + 10*x*y*z^4 + 4*x*z^5 + 8*y^6 + 4*y^5*z + y^4*z^2 + 10*y^3*z^3 + y^2*z^4 + 4*y*z^5 + 8*z^6) := by
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
  have hn : 0 ≤ (8*x^6 + 4*x^5*y + 4*x^5*z + x^4*y^2 + 10*x^4*y*z + x^4*z^2 + 10*x^3*y^3 - 26*x^3*y^2*z - 26*x^3*y*z^2 + 10*x^3*z^3 + x^2*y^4 - 26*x^2*y^3*z + 42*x^2*y^2*z^2 - 26*x^2*y*z^3 + x^2*z^4 + 4*x*y^5 + 10*x*y^4*z - 26*x*y^3*z^2 - 26*x*y^2*z^3 + 10*x*y*z^4 + 4*x*z^5 + 8*y^6 + 4*y^5*z + y^4*z^2 + 10*y^3*z^3 + y^2*z^4 + 4*y*z^5 + 8*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (2*x + y + z)^2 / (2 * x^2 + (y + z)^2) + (2*y + z + x)^2 / (2 * y^2 + (z + x)^2) + (2*z + x + y)^2 / (2 * z^2 + (x + y)^2) ≤ 8) := @solution
#print axioms solution
