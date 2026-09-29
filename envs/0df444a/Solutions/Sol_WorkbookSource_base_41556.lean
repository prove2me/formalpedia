-- Prove2me | solution 1 for WorkbookSource.base_41556
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:15:46.790602+00:00
-- url     : https://prove2.me/submissions/96d26f7e-74d0-4ed5-9848-e77d6cdaa355

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x / (y ^ 2 + z ^ 2) + y / (x ^ 2 + z ^ 2) + z / (x ^ 2 + y ^ 2) ≥ 3 * (x + y + z) / (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^7 + x^6*y + x^6*z - x^5*y^2 + x^5*y*z - x^5*z^2 - x^4*y^3 - x^4*y^2*z - x^4*y*z^2 - x^4*z^3 - x^3*y^4 + 3*x^3*y^3*z - x^3*y^2*z^2 + 3*x^3*y*z^3 - x^3*z^4 - x^2*y^5 - x^2*y^4*z - x^2*y^3*z^2 - x^2*y^2*z^3 - x^2*y*z^4 - x^2*z^5 + x*y^6 + x*y^5*z - x*y^4*z^2 + 3*x*y^3*z^3 - x*y^2*z^4 + x*y*z^5 + x*z^6 + y^7 + y^6*z - y^5*z^2 - y^4*z^3 - y^3*z^4 - y^2*z^5 + y*z^6 + z^7) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * x^5 * (y - x)^2 + (20 : ℝ) * x^5 * (y - x)^1 * (z - y)^1 + (20 : ℝ) * x^5 * (z - y)^2 + (48 : ℝ) * x^4 * (y - x)^3 + (72 : ℝ) * x^4 * (y - x)^2 * (z - y)^1 + (128 : ℝ) * x^4 * (y - x)^1 * (z - y)^2 + (52 : ℝ) * x^4 * (z - y)^3 + (48 : ℝ) * x^3 * (y - x)^4 + (96 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (264 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (216 : ℝ) * x^3 * (y - x)^1 * (z - y)^3 + (56 : ℝ) * x^3 * (z - y)^4 + (24 : ℝ) * x^2 * (y - x)^5 + (60 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (248 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (312 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (164 : ℝ) * x^2 * (y - x)^1 * (z - y)^4 + (32 : ℝ) * x^2 * (z - y)^5 + (5 : ℝ) * x^1 * (y - x)^6 + (15 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (107 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (189 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (151 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (59 : ℝ) * x^1 * (y - x)^1 * (z - y)^5 + (9 : ℝ) * x^1 * (z - y)^6 + (16 : ℝ) * (y - x)^5 * (z - y)^2 + (40 : ℝ) * (y - x)^4 * (z - y)^3 + (44 : ℝ) * (y - x)^3 * (z - y)^4 + (26 : ℝ) * (y - x)^2 * (z - y)^5 + (8 : ℝ) * (y - x)^1 * (z - y)^6 + (1 : ℝ) * (z - y)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^7 + x^6*y + x^6*z - x^5*y^2 + x^5*y*z - x^5*z^2 - x^4*y^3 - x^4*y^2*z - x^4*y*z^2 - x^4*z^3 - x^3*y^4 + 3*x^3*y^3*z - x^3*y^2*z^2 + 3*x^3*y*z^3 - x^3*z^4 - x^2*y^5 - x^2*y^4*z - x^2*y^3*z^2 - x^2*y^2*z^3 - x^2*y*z^4 - x^2*z^5 + x*y^6 + x*y^5*z - x*y^4*z^2 + 3*x*y^3*z^3 - x*y^2*z^4 + x*y*z^5 + x*z^6 + y^7 + y^6*z - y^5*z^2 - y^4*z^3 - y^3*z^4 - y^2*z^5 + y*z^6 + z^7) := by
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
  have hn : 0 ≤ (x^7 + x^6*y + x^6*z - x^5*y^2 + x^5*y*z - x^5*z^2 - x^4*y^3 - x^4*y^2*z - x^4*y*z^2 - x^4*z^3 - x^3*y^4 + 3*x^3*y^3*z - x^3*y^2*z^2 + 3*x^3*y*z^3 - x^3*z^4 - x^2*y^5 - x^2*y^4*z - x^2*y^3*z^2 - x^2*y^2*z^3 - x^2*y*z^4 - x^2*z^5 + x*y^6 + x*y^5*z - x*y^4*z^2 + 3*x*y^3*z^3 - x*y^2*z^4 + x*y*z^5 + x*z^6 + y^7 + y^6*z - y^5*z^2 - y^4*z^3 - y^3*z^4 - y^2*z^5 + y*z^6 + z^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x / (y ^ 2 + z ^ 2) + y / (x ^ 2 + z ^ 2) + z / (x ^ 2 + y ^ 2) ≥ 3 * (x + y + z) / (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x)) := @solution
#print axioms solution
