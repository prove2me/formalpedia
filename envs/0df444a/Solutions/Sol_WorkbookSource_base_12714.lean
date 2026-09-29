-- Prove2me | solution 1 for WorkbookSource.base_12714
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:46:37.387915+00:00
-- url     : https://prove2.me/submissions/b84eedd3-476f-4179-a90d-36998dde606a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 * (y + z) / (x^2 + 2 * y * z) + y^2 * (z + x) / (y^2 + 2 * z * x) + z^2 * (x + y) / (z^2 + 2 * x * y)) ≤ (2 * (x^2 + y^2 + z^2)) / (x + y + z)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (8*x^6*y*z + 2*x^5*y^3 - 4*x^5*y^2*z - 4*x^5*y*z^2 + 2*x^5*z^3 - 4*x^4*y^4 - 2*x^4*y^3*z + 8*x^4*y^2*z^2 - 2*x^4*y*z^3 - 4*x^4*z^4 + 2*x^3*y^5 - 2*x^3*y^4*z - 4*x^3*y^3*z^2 - 4*x^3*y^2*z^3 - 2*x^3*y*z^4 + 2*x^3*z^5 - 4*x^2*y^5*z + 8*x^2*y^4*z^2 - 4*x^2*y^3*z^3 + 8*x^2*y^2*z^4 - 4*x^2*y*z^5 + 8*x*y^6*z - 4*x*y^5*z^2 - 2*x*y^4*z^3 - 2*x*y^3*z^4 - 4*x*y^2*z^5 + 8*x*y*z^6 + 2*y^5*z^3 - 4*y^4*z^4 + 2*y^3*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * x^6 * (y - x)^2 + (36 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (36 : ℝ) * x^6 * (z - y)^2 + (120 : ℝ) * x^5 * (y - x)^3 + (180 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (252 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (96 : ℝ) * x^5 * (z - y)^3 + (156 : ℝ) * x^4 * (y - x)^4 + (312 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (588 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (432 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (96 : ℝ) * x^4 * (z - y)^4 + (100 : ℝ) * x^3 * (y - x)^5 + (250 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (628 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (692 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (302 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (44 : ℝ) * x^3 * (z - y)^5 + (32 : ℝ) * x^2 * (y - x)^6 + (96 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (324 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (488 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (318 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (90 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (8 : ℝ) * x^2 * (z - y)^6 + (4 : ℝ) * x^1 * (y - x)^7 + (14 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (70 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (140 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (122 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (50 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (8 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (2 : ℝ) * (y - x)^6 * (z - y)^2 + (6 : ℝ) * (y - x)^5 * (z - y)^3 + (6 : ℝ) * (y - x)^4 * (z - y)^4 + (2 : ℝ) * (y - x)^3 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*x^6*y*z + 2*x^5*y^3 - 4*x^5*y^2*z - 4*x^5*y*z^2 + 2*x^5*z^3 - 4*x^4*y^4 - 2*x^4*y^3*z + 8*x^4*y^2*z^2 - 2*x^4*y*z^3 - 4*x^4*z^4 + 2*x^3*y^5 - 2*x^3*y^4*z - 4*x^3*y^3*z^2 - 4*x^3*y^2*z^3 - 2*x^3*y*z^4 + 2*x^3*z^5 - 4*x^2*y^5*z + 8*x^2*y^4*z^2 - 4*x^2*y^3*z^3 + 8*x^2*y^2*z^4 - 4*x^2*y*z^5 + 8*x*y^6*z - 4*x*y^5*z^2 - 2*x*y^4*z^3 - 2*x*y^3*z^4 - 4*x*y^2*z^5 + 8*x*y*z^6 + 2*y^5*z^3 - 4*y^4*z^4 + 2*y^3*z^5) := by
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
  have hn : 0 ≤ (8*x^6*y*z + 2*x^5*y^3 - 4*x^5*y^2*z - 4*x^5*y*z^2 + 2*x^5*z^3 - 4*x^4*y^4 - 2*x^4*y^3*z + 8*x^4*y^2*z^2 - 2*x^4*y*z^3 - 4*x^4*z^4 + 2*x^3*y^5 - 2*x^3*y^4*z - 4*x^3*y^3*z^2 - 4*x^3*y^2*z^3 - 2*x^3*y*z^4 + 2*x^3*z^5 - 4*x^2*y^5*z + 8*x^2*y^4*z^2 - 4*x^2*y^3*z^3 + 8*x^2*y^2*z^4 - 4*x^2*y*z^5 + 8*x*y^6*z - 4*x*y^5*z^2 - 2*x*y^4*z^3 - 2*x*y^3*z^4 - 4*x*y^2*z^5 + 8*x*y*z^6 + 2*y^5*z^3 - 4*y^4*z^4 + 2*y^3*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x^2 * (y + z) / (x^2 + 2 * y * z) + y^2 * (z + x) / (y^2 + 2 * z * x) + z^2 * (x + y) / (z^2 + 2 * x * y)) ≤ (2 * (x^2 + y^2 + z^2)) / (x + y + z)) := @solution
#print axioms solution
