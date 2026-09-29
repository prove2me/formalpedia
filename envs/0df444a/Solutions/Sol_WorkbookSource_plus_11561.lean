-- Prove2me | solution 1 for WorkbookSource.plus_11561
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:09:02.735579+00:00
-- url     : https://prove2.me/submissions/9ed0ec52-cf9c-4aee-93d3-0bf6eac84123

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y ^ 2 + y * z + z ^ 2) + y / (x ^ 2 + x * z + z ^ 2) + z / (x ^ 2 + x * y + y ^ 2)) ≥ 4 / (x + y + z + 3 * (x ^ 3 + y ^ 3 + z ^ 3) / (x + y + z) ^ 2)   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (4*x^8 + 7*x^7*y + 7*x^7*z + 6*x^6*y^2 + 12*x^6*y*z + 6*x^6*z^2 + 2*x^5*y^3 + 6*x^5*y^2*z + 6*x^5*y*z^2 + 2*x^5*z^3 - 2*x^4*y^4 - 12*x^4*y^3*z - 12*x^4*y^2*z^2 - 12*x^4*y*z^3 - 2*x^4*z^4 + 2*x^3*y^5 - 12*x^3*y^4*z - 20*x^3*y^3*z^2 - 20*x^3*y^2*z^3 - 12*x^3*y*z^4 + 2*x^3*z^5 + 6*x^2*y^6 + 6*x^2*y^5*z - 12*x^2*y^4*z^2 - 20*x^2*y^3*z^3 - 12*x^2*y^2*z^4 + 6*x^2*y*z^5 + 6*x^2*z^6 + 7*x*y^7 + 12*x*y^6*z + 6*x*y^5*z^2 - 12*x*y^4*z^3 - 12*x*y^3*z^4 + 6*x*y^2*z^5 + 12*x*y*z^6 + 7*x*z^7 + 4*y^8 + 7*y^7*z + 6*y^6*z^2 + 2*y^5*z^3 - 2*y^4*z^4 + 2*y^3*z^5 + 6*y^2*z^6 + 7*y*z^7 + 4*z^8) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (486 : ℝ) * x^6 * (y - x)^2 + (486 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (486 : ℝ) * x^6 * (z - y)^2 + (1782 : ℝ) * x^5 * (y - x)^3 + (2673 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (3159 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (1134 : ℝ) * x^5 * (z - y)^3 + (2790 : ℝ) * x^4 * (y - x)^4 + (5580 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (7965 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (5175 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (1170 : ℝ) * x^4 * (z - y)^4 + (2382 : ℝ) * x^3 * (y - x)^5 + (5955 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (10122 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (9228 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (4035 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (678 : ℝ) * x^3 * (z - y)^5 + (1170 : ℝ) * x^2 * (y - x)^6 + (3510 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (6966 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (8082 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (5175 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (1719 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (234 : ℝ) * x^2 * (z - y)^6 + (314 : ℝ) * x^1 * (y - x)^7 + (1099 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (2499 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (3500 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (2935 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (1452 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (395 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (46 : ℝ) * x^1 * (z - y)^7 + (36 : ℝ) * (y - x)^8 + (144 : ℝ) * (y - x)^7 * (z - y)^1 + (369 : ℝ) * (y - x)^6 * (z - y)^2 + (603 : ℝ) * (y - x)^5 * (z - y)^3 + (623 : ℝ) * (y - x)^4 * (z - y)^4 + (409 : ℝ) * (y - x)^3 * (z - y)^5 + (167 : ℝ) * (y - x)^2 * (z - y)^6 + (39 : ℝ) * (y - x)^1 * (z - y)^7 + (4 : ℝ) * (z - y)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*x^8 + 7*x^7*y + 7*x^7*z + 6*x^6*y^2 + 12*x^6*y*z + 6*x^6*z^2 + 2*x^5*y^3 + 6*x^5*y^2*z + 6*x^5*y*z^2 + 2*x^5*z^3 - 2*x^4*y^4 - 12*x^4*y^3*z - 12*x^4*y^2*z^2 - 12*x^4*y*z^3 - 2*x^4*z^4 + 2*x^3*y^5 - 12*x^3*y^4*z - 20*x^3*y^3*z^2 - 20*x^3*y^2*z^3 - 12*x^3*y*z^4 + 2*x^3*z^5 + 6*x^2*y^6 + 6*x^2*y^5*z - 12*x^2*y^4*z^2 - 20*x^2*y^3*z^3 - 12*x^2*y^2*z^4 + 6*x^2*y*z^5 + 6*x^2*z^6 + 7*x*y^7 + 12*x*y^6*z + 6*x*y^5*z^2 - 12*x*y^4*z^3 - 12*x*y^3*z^4 + 6*x*y^2*z^5 + 12*x*y*z^6 + 7*x*z^7 + 4*y^8 + 7*y^7*z + 6*y^6*z^2 + 2*y^5*z^3 - 2*y^4*z^4 + 2*y^3*z^5 + 6*y^2*z^6 + 7*y*z^7 + 4*z^8) := by
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
  have hn : 0 ≤ ((x + y + z)*(4*x^7 + 3*x^6*y + 3*x^6*z + 3*x^5*y^2 + 6*x^5*y*z + 3*x^5*z^2 - x^4*y^3 - 3*x^4*y^2*z - 3*x^4*y*z^2 - x^4*z^3 - x^3*y^4 - 8*x^3*y^3*z - 6*x^3*y^2*z^2 - 8*x^3*y*z^3 - x^3*z^4 + 3*x^2*y^5 - 3*x^2*y^4*z - 6*x^2*y^3*z^2 - 6*x^2*y^2*z^3 - 3*x^2*y*z^4 + 3*x^2*z^5 + 3*x*y^6 + 6*x*y^5*z - 3*x*y^4*z^2 - 8*x*y^3*z^3 - 3*x*y^2*z^4 + 6*x*y*z^5 + 3*x*z^6 + 4*y^7 + 3*y^6*z + 3*y^5*z^2 - y^4*z^3 - y^3*z^4 + 3*y^2*z^5 + 3*y*z^6 + 4*z^7)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x / (y ^ 2 + y * z + z ^ 2) + y / (x ^ 2 + x * z + z ^ 2) + z / (x ^ 2 + x * y + y ^ 2)) ≥ 4 / (x + y + z + 3 * (x ^ 3 + y ^ 3 + z ^ 3) / (x + y + z) ^ 2)) := @solution
#print axioms solution
