-- Prove2me | solution 1 for WorkbookSource.base_46677
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:15:13.922751+00:00
-- url     : https://prove2.me/submissions/948f7ce5-736b-415d-b130-7b669229a1f0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) ^ 2 * x ^ 6 + (y + z) ^ 3 * x ^ 5 + y * z * (3 * z ^ 2 + 3 * y ^ 2 - 58 * y * z) * x ^ 4 + (z ^ 2 + 4 * y * z + y ^ 2) * (y + z) ^ 3 * x ^ 3 + (z ^ 4 + z ^ 3 * y + y ^ 3 * z + y ^ 4 + 3 * y ^ 2 * z ^ 2) * (y + z) ^ 2 * x ^ 2 - y * z * (2 * z ^ 2 + 3 * y * z + 2 * y ^ 2) * (y + z) ^ 3 * x + y ^ 2 * z ^ 2 * (y ^ 2 + z ^ 2 + 3 * y * z) * (y + z) ^ 2 ≥ 0  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6*y^2 + 2*x^6*y*z + x^6*z^2 + x^5*y^3 + 3*x^5*y^2*z + 3*x^5*y*z^2 + x^5*z^3 + 3*x^4*y^3*z - 58*x^4*y^2*z^2 + 3*x^4*y*z^3 + x^3*y^5 + 7*x^3*y^4*z + 16*x^3*y^3*z^2 + 16*x^3*y^2*z^3 + 7*x^3*y*z^4 + x^3*z^5 + x^2*y^6 + 3*x^2*y^5*z + 6*x^2*y^4*z^2 + 8*x^2*y^3*z^3 + 6*x^2*y^2*z^4 + 3*x^2*y*z^5 + x^2*z^6 - 2*x*y^6*z - 9*x*y^5*z^2 - 17*x*y^4*z^3 - 17*x*y^3*z^4 - 9*x*y^2*z^5 - 2*x*y*z^6 + y^6*z^2 + 5*y^5*z^3 + 8*y^4*z^4 + 5*y^3*z^5 + y^2*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * x^6 * (z - y)^2 + (64 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (32 : ℝ) * x^5 * (z - y)^3 + (48 : ℝ) * x^4 * (y - x)^4 + (96 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (80 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (32 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (4 : ℝ) * x^4 * (z - y)^4 + (160 : ℝ) * x^3 * (y - x)^5 + (400 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (320 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (80 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (196 : ℝ) * x^2 * (y - x)^6 + (588 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (636 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (292 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (48 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (104 : ℝ) * x^1 * (y - x)^7 + (364 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (492 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (320 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (100 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (12 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (20 : ℝ) * (y - x)^8 + (80 : ℝ) * (y - x)^7 * (z - y)^1 + (129 : ℝ) * (y - x)^6 * (z - y)^2 + (107 : ℝ) * (y - x)^5 * (z - y)^3 + (48 : ℝ) * (y - x)^4 * (z - y)^4 + (11 : ℝ) * (y - x)^3 * (z - y)^5 + (1 : ℝ) * (y - x)^2 * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ x) (hord2 : x ≤ z) : 0 ≤ (x^6*y^2 + 2*x^6*y*z + x^6*z^2 + x^5*y^3 + 3*x^5*y^2*z + 3*x^5*y*z^2 + x^5*z^3 + 3*x^4*y^3*z - 58*x^4*y^2*z^2 + 3*x^4*y*z^3 + x^3*y^5 + 7*x^3*y^4*z + 16*x^3*y^3*z^2 + 16*x^3*y^2*z^3 + 7*x^3*y*z^4 + x^3*z^5 + x^2*y^6 + 3*x^2*y^5*z + 6*x^2*y^4*z^2 + 8*x^2*y^3*z^3 + 6*x^2*y^2*z^4 + 3*x^2*y*z^5 + x^2*z^6 - 2*x*y^6*z - 9*x*y^5*z^2 - 17*x*y^4*z^3 - 17*x*y^3*z^4 - 9*x*y^2*z^5 - 2*x*y*z^6 + y^6*z^2 + 5*y^5*z^3 + 8*y^4*z^4 + 5*y^3*z^5 + y^2*z^6) := by
    have hdiff1 : 0 ≤ (x - y) := by linarith
    have hdiff2 : 0 ≤ (z - x) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * y^6 * (x - y)^2 + (64 : ℝ) * y^6 * (x - y)^1 * (z - x)^1 + (32 : ℝ) * y^6 * (z - x)^2 + (160 : ℝ) * y^5 * (x - y)^3 + (352 : ℝ) * y^5 * (x - y)^2 * (z - x)^1 + (224 : ℝ) * y^5 * (x - y)^1 * (z - x)^2 + (32 : ℝ) * y^5 * (z - x)^3 + (324 : ℝ) * y^4 * (x - y)^4 + (784 : ℝ) * y^4 * (x - y)^3 * (z - x)^1 + (648 : ℝ) * y^4 * (x - y)^2 * (z - x)^2 + (144 : ℝ) * y^4 * (x - y)^1 * (z - x)^3 + (4 : ℝ) * y^4 * (z - x)^4 + (336 : ℝ) * y^3 * (x - y)^5 + (896 : ℝ) * y^3 * (x - y)^4 * (z - x)^1 + (912 : ℝ) * y^3 * (x - y)^3 * (z - x)^2 + (336 : ℝ) * y^3 * (x - y)^2 * (z - x)^3 + (16 : ℝ) * y^3 * (x - y)^1 * (z - x)^4 + (184 : ℝ) * y^2 * (x - y)^6 + (544 : ℝ) * y^2 * (x - y)^5 * (z - x)^1 + (656 : ℝ) * y^2 * (x - y)^4 * (z - x)^2 + (364 : ℝ) * y^2 * (x - y)^3 * (z - x)^3 + (72 : ℝ) * y^2 * (x - y)^2 * (z - x)^4 + (48 : ℝ) * y^1 * (x - y)^7 + (160 : ℝ) * y^1 * (x - y)^6 * (z - x)^1 + (228 : ℝ) * y^1 * (x - y)^5 * (z - x)^2 + (176 : ℝ) * y^1 * (x - y)^4 * (z - x)^3 + (72 : ℝ) * y^1 * (x - y)^3 * (z - x)^4 + (12 : ℝ) * y^1 * (x - y)^2 * (z - x)^5 + (4 : ℝ) * (x - y)^8 + (16 : ℝ) * (x - y)^7 * (z - x)^1 + (29 : ℝ) * (x - y)^6 * (z - x)^2 + (31 : ℝ) * (x - y)^5 * (z - x)^3 + (20 : ℝ) * (x - y)^4 * (z - x)^4 + (7 : ℝ) * (x - y)^3 * (z - x)^5 + (1 : ℝ) * (x - y)^2 * (z - x)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (x y z : ℝ) (hlow : 0 ≤ y) (hord1 : y ≤ z) (hord2 : z ≤ x) : 0 ≤ (x^6*y^2 + 2*x^6*y*z + x^6*z^2 + x^5*y^3 + 3*x^5*y^2*z + 3*x^5*y*z^2 + x^5*z^3 + 3*x^4*y^3*z - 58*x^4*y^2*z^2 + 3*x^4*y*z^3 + x^3*y^5 + 7*x^3*y^4*z + 16*x^3*y^3*z^2 + 16*x^3*y^2*z^3 + 7*x^3*y*z^4 + x^3*z^5 + x^2*y^6 + 3*x^2*y^5*z + 6*x^2*y^4*z^2 + 8*x^2*y^3*z^3 + 6*x^2*y^2*z^4 + 3*x^2*y*z^5 + x^2*z^6 - 2*x*y^6*z - 9*x*y^5*z^2 - 17*x*y^4*z^3 - 17*x*y^3*z^4 - 9*x*y^2*z^5 - 2*x*y*z^6 + y^6*z^2 + 5*y^5*z^3 + 8*y^4*z^4 + 5*y^3*z^5 + y^2*z^6) := by
    have hdiff1 : 0 ≤ (z - y) := by linarith
    have hdiff2 : 0 ≤ (x - z) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * y^6 * (z - y)^2 + (160 : ℝ) * y^5 * (z - y)^3 + (128 : ℝ) * y^5 * (z - y)^2 * (x - z)^1 + (324 : ℝ) * y^4 * (z - y)^4 + (512 : ℝ) * y^4 * (z - y)^3 * (x - z)^1 + (240 : ℝ) * y^4 * (z - y)^2 * (x - z)^2 + (96 : ℝ) * y^4 * (z - y)^1 * (x - z)^3 + (48 : ℝ) * y^4 * (x - z)^4 + (336 : ℝ) * y^3 * (z - y)^5 + (784 : ℝ) * y^3 * (z - y)^4 * (x - z)^1 + (688 : ℝ) * y^3 * (z - y)^3 * (x - z)^2 + (384 : ℝ) * y^3 * (z - y)^2 * (x - z)^3 + (176 : ℝ) * y^3 * (z - y)^1 * (x - z)^4 + (32 : ℝ) * y^3 * (x - z)^5 + (184 : ℝ) * y^2 * (z - y)^6 + (560 : ℝ) * y^2 * (z - y)^5 * (x - z)^1 + (696 : ℝ) * y^2 * (z - y)^4 * (x - z)^2 + (500 : ℝ) * y^2 * (z - y)^3 * (x - z)^3 + (236 : ℝ) * y^2 * (z - y)^2 * (x - z)^4 + (60 : ℝ) * y^2 * (z - y)^1 * (x - z)^5 + (4 : ℝ) * y^2 * (x - z)^6 + (48 : ℝ) * y^1 * (z - y)^7 + (176 : ℝ) * y^1 * (z - y)^6 * (x - z)^1 + (276 : ℝ) * y^1 * (z - y)^5 * (x - z)^2 + (244 : ℝ) * y^1 * (z - y)^4 * (x - z)^3 + (128 : ℝ) * y^1 * (z - y)^3 * (x - z)^4 + (36 : ℝ) * y^1 * (z - y)^2 * (x - z)^5 + (4 : ℝ) * y^1 * (z - y)^1 * (x - z)^6 + (4 : ℝ) * (z - y)^8 + (16 : ℝ) * (z - y)^7 * (x - z)^1 + (29 : ℝ) * (z - y)^6 * (x - z)^2 + (31 : ℝ) * (z - y)^5 * (x - z)^3 + (20 : ℝ) * (z - y)^4 * (x - z)^4 + (7 : ℝ) * (z - y)^3 * (x - z)^5 + (1 : ℝ) * (z - y)^2 * (x - z)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6*y^2 + 2*x^6*y*z + x^6*z^2 + x^5*y^3 + 3*x^5*y^2*z + 3*x^5*y*z^2 + x^5*z^3 + 3*x^4*y^3*z - 58*x^4*y^2*z^2 + 3*x^4*y*z^3 + x^3*y^5 + 7*x^3*y^4*z + 16*x^3*y^3*z^2 + 16*x^3*y^2*z^3 + 7*x^3*y*z^4 + x^3*z^5 + x^2*y^6 + 3*x^2*y^5*z + 6*x^2*y^4*z^2 + 8*x^2*y^3*z^3 + 6*x^2*y^2*z^4 + 3*x^2*y*z^5 + x^2*z^6 - 2*x*y^6*z - 9*x*y^5*z^2 - 17*x*y^4*z^3 - 17*x*y^3*z^4 - 9*x*y^2*z^5 - 2*x*y*z^6 + y^6*z^2 + 5*y^5*z^3 + 8*y^4*z^4 + 5*y^3*z^5 + y^2*z^6) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux0 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux1 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux2 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (y + z) ^ 2 * x ^ 6 + (y + z) ^ 3 * x ^ 5 + y * z * (3 * z ^ 2 + 3 * y ^ 2 - 58 * y * z) * x ^ 4 + (z ^ 2 + 4 * y * z + y ^ 2) * (y + z) ^ 3 * x ^ 3 + (z ^ 4 + z ^ 3 * y + y ^ 3 * z + y ^ 4 + 3 * y ^ 2 * z ^ 2) * (y + z) ^ 2 * x ^ 2 - y * z * (2 * z ^ 2 + 3 * y * z + 2 * y ^ 2) * (y + z) ^ 3 * x + y ^ 2 * z ^ 2 * (y ^ 2 + z ^ 2 + 3 * y * z) * (y + z) ^ 2 ≥ 0) := @solution
#print axioms solution
