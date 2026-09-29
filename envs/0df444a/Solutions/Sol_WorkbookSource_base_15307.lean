-- Prove2me | solution 1 for WorkbookSource.base_15307
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:01.965188+00:00
-- url     : https://prove2.me/submissions/e3baeadb-5a7b-4eca-a756-7bbf156dd8aa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (4 * x ^ 2 + 4 * y ^ 2 + z ^ 2) + y / (4 * y ^ 2 + 4 * z ^ 2 + x ^ 2) + z / (4 * z ^ 2 + 4 * x ^ 2 + y ^ 2)) ≤ 1 / (x + y + z)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (12*x^6 - 20*x^5*y - 8*x^5*z + 51*x^4*y^2 - 20*x^4*y*z + 60*x^4*z^2 - 37*x^3*y^3 - 37*x^3*y^2*z - 40*x^3*y*z^2 - 37*x^3*z^3 + 60*x^2*y^4 - 40*x^2*y^3*z + 117*x^2*y^2*z^2 - 37*x^2*y*z^3 + 51*x^2*z^4 - 8*x*y^5 - 20*x*y^4*z - 37*x*y^3*z^2 - 40*x*y^2*z^3 - 20*x*y*z^4 - 20*x*z^5 + 12*y^6 - 20*y^5*z + 51*y^4*z^2 - 37*y^3*z^3 + 60*y^2*z^4 - 8*y*z^5 + 12*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (144 : ℝ) * x^4 * (y - x)^2 + (144 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (144 : ℝ) * x^4 * (z - y)^2 + (403 : ℝ) * x^3 * (y - x)^3 + (699 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (642 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (173 : ℝ) * x^3 * (z - y)^3 + (476 : ℝ) * x^2 * (y - x)^4 + (1141 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (1281 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (616 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (131 : ℝ) * x^2 * (z - y)^4 + (275 : ℝ) * x^1 * (y - x)^5 + (821 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (1123 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (769 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (280 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (44 : ℝ) * x^1 * (z - y)^5 + (70 : ℝ) * (y - x)^6 + (243 : ℝ) * (y - x)^5 * (z - y)^1 + (400 : ℝ) * (y - x)^4 * (z - y)^2 + (363 : ℝ) * (y - x)^3 * (z - y)^3 + (200 : ℝ) * (y - x)^2 * (z - y)^4 + (64 : ℝ) * (y - x)^1 * (z - y)^5 + (12 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (12*x^6 - 20*x^5*y - 8*x^5*z + 51*x^4*y^2 - 20*x^4*y*z + 60*x^4*z^2 - 37*x^3*y^3 - 37*x^3*y^2*z - 40*x^3*y*z^2 - 37*x^3*z^3 + 60*x^2*y^4 - 40*x^2*y^3*z + 117*x^2*y^2*z^2 - 37*x^2*y*z^3 + 51*x^2*z^4 - 8*x*y^5 - 20*x*y^4*z - 37*x*y^3*z^2 - 40*x*y^2*z^3 - 20*x*y*z^4 - 20*x*z^5 + 12*y^6 - 20*y^5*z + 51*y^4*z^2 - 37*y^3*z^3 + 60*y^2*z^4 - 8*y*z^5 + 12*z^6) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (144 : ℝ) * x^4 * (z - x)^2 + (144 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (144 : ℝ) * x^4 * (y - z)^2 + (403 : ℝ) * x^3 * (z - x)^3 + (510 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (453 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (173 : ℝ) * x^3 * (y - z)^3 + (476 : ℝ) * x^2 * (z - x)^4 + (763 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (714 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (427 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (131 : ℝ) * x^2 * (y - z)^4 + (275 : ℝ) * x^1 * (z - x)^5 + (554 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (589 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (424 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (202 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (44 : ℝ) * x^1 * (y - z)^5 + (70 : ℝ) * (z - x)^6 + (177 : ℝ) * (z - x)^5 * (y - z)^1 + (235 : ℝ) * (z - x)^4 * (y - z)^2 + (207 : ℝ) * (z - x)^3 * (y - z)^3 + (131 : ℝ) * (z - x)^2 * (y - z)^4 + (52 : ℝ) * (z - x)^1 * (y - z)^5 + (12 : ℝ) * (y - z)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (12*x^6 - 20*x^5*y - 8*x^5*z + 51*x^4*y^2 - 20*x^4*y*z + 60*x^4*z^2 - 37*x^3*y^3 - 37*x^3*y^2*z - 40*x^3*y*z^2 - 37*x^3*z^3 + 60*x^2*y^4 - 40*x^2*y^3*z + 117*x^2*y^2*z^2 - 37*x^2*y*z^3 + 51*x^2*z^4 - 8*x*y^5 - 20*x*y^4*z - 37*x*y^3*z^2 - 40*x*y^2*z^3 - 20*x*y*z^4 - 20*x*z^5 + 12*y^6 - 20*y^5*z + 51*y^4*z^2 - 37*y^3*z^3 + 60*y^2*z^4 - 8*y*z^5 + 12*z^6) := by
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
  have hn : 0 ≤ (12*x^6 - 20*x^5*y - 8*x^5*z + 51*x^4*y^2 - 20*x^4*y*z + 60*x^4*z^2 - 37*x^3*y^3 - 37*x^3*y^2*z - 40*x^3*y*z^2 - 37*x^3*z^3 + 60*x^2*y^4 - 40*x^2*y^3*z + 117*x^2*y^2*z^2 - 37*x^2*y*z^3 + 51*x^2*z^4 - 8*x*y^5 - 20*x*y^4*z - 37*x*y^3*z^2 - 40*x*y^2*z^3 - 20*x*y*z^4 - 20*x*z^5 + 12*y^6 - 20*y^5*z + 51*y^4*z^2 - 37*y^3*z^3 + 60*y^2*z^4 - 8*y*z^5 + 12*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x / (4 * x ^ 2 + 4 * y ^ 2 + z ^ 2) + y / (4 * y ^ 2 + 4 * z ^ 2 + x ^ 2) + z / (4 * z ^ 2 + 4 * x ^ 2 + y ^ 2)) ≤ 1 / (x + y + z)) := @solution
#print axioms solution
