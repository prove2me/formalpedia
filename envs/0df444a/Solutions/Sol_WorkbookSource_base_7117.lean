-- Prove2me | solution 1 for WorkbookSource.base_7117
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:27:02.145815+00:00
-- url     : https://prove2.me/submissions/3426ff5c-0b3b-4b4d-8e3e-9c7aba4e52c0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 * y * z / x ^ 2 + 2 * x * z / y ^ 2 + 4 * x * y / z ^ 2 ≥ 3 + y / x + z / x + 2 * x / z + 2 * y / z  := by
  have hp : 0 ≤ (4*x^3*y^3 - 2*x^3*y^2*z + 2*x^3*z^3 - 2*x^2*y^3*z - 3*x^2*y^2*z^2 - x*y^3*z^2 - x*y^2*z^3 + 3*y^3*z^3) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (y - x) := by linarith
        have hdiff2 : 0 ≤ (z - y) := by linarith
        have hpos : 0 ≤ (7 : ℝ) * x^4 * (y - x)^2 + (9 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (8 : ℝ) * x^4 * (z - y)^2 + (24 : ℝ) * x^3 * (y - x)^3 + (40 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (24 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (4 : ℝ) * x^3 * (z - y)^3 + (30 : ℝ) * x^2 * (y - x)^4 + (62 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (39 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (7 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (16 : ℝ) * x^1 * (y - x)^5 + (40 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (32 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (8 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (3 : ℝ) * (y - x)^6 + (9 : ℝ) * (y - x)^5 * (z - y)^1 + (9 : ℝ) * (y - x)^4 * (z - y)^2 + (3 : ℝ) * (y - x)^3 * (z - y)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - x) := by linarith
          have hdiff2 : 0 ≤ (y - z) := by linarith
          have hpos : 0 ≤ (7 : ℝ) * x^4 * (z - x)^2 + (5 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (6 : ℝ) * x^4 * (y - z)^2 + (24 : ℝ) * x^3 * (z - x)^3 + (32 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (16 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (4 : ℝ) * x^3 * (y - z)^3 + (30 : ℝ) * x^2 * (z - x)^4 + (58 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (33 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (5 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (16 : ℝ) * x^1 * (z - x)^5 + (40 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (32 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (8 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (3 : ℝ) * (z - x)^6 + (9 : ℝ) * (z - x)^5 * (y - z)^1 + (9 : ℝ) * (z - x)^4 * (y - z)^2 + (3 : ℝ) * (z - x)^3 * (y - z)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (x - z) := by linarith
          have hdiff2 : 0 ≤ (y - x) := by linarith
          have hpos : 0 ≤ (8 : ℝ) * z^4 * (x - z)^2 + (7 : ℝ) * z^4 * (x - z)^1 * (y - x)^1 + (6 : ℝ) * z^4 * (y - x)^2 + (28 : ℝ) * z^3 * (x - z)^3 + (40 : ℝ) * z^3 * (x - z)^2 * (y - x)^1 + (20 : ℝ) * z^3 * (x - z)^1 * (y - x)^2 + (4 : ℝ) * z^3 * (y - x)^3 + (36 : ℝ) * z^2 * (x - z)^4 + (71 : ℝ) * z^2 * (x - z)^3 * (y - x)^1 + (42 : ℝ) * z^2 * (x - z)^2 * (y - x)^2 + (7 : ℝ) * z^2 * (x - z)^1 * (y - x)^3 + (20 : ℝ) * z^1 * (x - z)^5 + (50 : ℝ) * z^1 * (x - z)^4 * (y - x)^1 + (40 : ℝ) * z^1 * (x - z)^3 * (y - x)^2 + (10 : ℝ) * z^1 * (x - z)^2 * (y - x)^3 + (4 : ℝ) * (x - z)^6 + (12 : ℝ) * (x - z)^5 * (y - x)^1 + (12 : ℝ) * (x - z)^4 * (y - x)^2 + (4 : ℝ) * (x - z)^3 * (y - x)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (x - y) := by linarith
        have hdiff2 : 0 ≤ (z - x) := by linarith
        have hpos : 0 ≤ (6 : ℝ) * y^4 * (x - y)^2 + (7 : ℝ) * y^4 * (x - y)^1 * (z - x)^1 + (8 : ℝ) * y^4 * (z - x)^2 + (20 : ℝ) * y^3 * (x - y)^3 + (32 : ℝ) * y^3 * (x - y)^2 * (z - x)^1 + (20 : ℝ) * y^3 * (x - y)^1 * (z - x)^2 + (4 : ℝ) * y^3 * (z - x)^3 + (24 : ℝ) * y^2 * (x - y)^4 + (49 : ℝ) * y^2 * (x - y)^3 * (z - x)^1 + (30 : ℝ) * y^2 * (x - y)^2 * (z - x)^2 + (5 : ℝ) * y^2 * (x - y)^1 * (z - x)^3 + (12 : ℝ) * y^1 * (x - y)^5 + (30 : ℝ) * y^1 * (x - y)^4 * (z - x)^1 + (24 : ℝ) * y^1 * (x - y)^3 * (z - x)^2 + (6 : ℝ) * y^1 * (x - y)^2 * (z - x)^3 + (2 : ℝ) * (x - y)^6 + (6 : ℝ) * (x - y)^5 * (z - x)^1 + (6 : ℝ) * (x - y)^4 * (z - x)^2 + (2 : ℝ) * (x - y)^3 * (z - x)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - y) := by linarith
          have hdiff2 : 0 ≤ (x - z) := by linarith
          have hpos : 0 ≤ (6 : ℝ) * y^4 * (z - y)^2 + (5 : ℝ) * y^4 * (z - y)^1 * (x - z)^1 + (7 : ℝ) * y^4 * (x - z)^2 + (20 : ℝ) * y^3 * (z - y)^3 + (28 : ℝ) * y^3 * (z - y)^2 * (x - z)^1 + (16 : ℝ) * y^3 * (z - y)^1 * (x - z)^2 + (4 : ℝ) * y^3 * (x - z)^3 + (24 : ℝ) * y^2 * (z - y)^4 + (47 : ℝ) * y^2 * (z - y)^3 * (x - z)^1 + (27 : ℝ) * y^2 * (z - y)^2 * (x - z)^2 + (4 : ℝ) * y^2 * (z - y)^1 * (x - z)^3 + (12 : ℝ) * y^1 * (z - y)^5 + (30 : ℝ) * y^1 * (z - y)^4 * (x - z)^1 + (24 : ℝ) * y^1 * (z - y)^3 * (x - z)^2 + (6 : ℝ) * y^1 * (z - y)^2 * (x - z)^3 + (2 : ℝ) * (z - y)^6 + (6 : ℝ) * (z - y)^5 * (x - z)^1 + (6 : ℝ) * (z - y)^4 * (x - z)^2 + (2 : ℝ) * (z - y)^3 * (x - z)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (y - z) := by linarith
          have hdiff2 : 0 ≤ (x - y) := by linarith
          have hpos : 0 ≤ (8 : ℝ) * z^4 * (y - z)^2 + (9 : ℝ) * z^4 * (y - z)^1 * (x - y)^1 + (7 : ℝ) * z^4 * (x - y)^2 + (28 : ℝ) * z^3 * (y - z)^3 + (44 : ℝ) * z^3 * (y - z)^2 * (x - y)^1 + (24 : ℝ) * z^3 * (y - z)^1 * (x - y)^2 + (4 : ℝ) * z^3 * (x - y)^3 + (36 : ℝ) * z^2 * (y - z)^4 + (73 : ℝ) * z^2 * (y - z)^3 * (x - y)^1 + (45 : ℝ) * z^2 * (y - z)^2 * (x - y)^2 + (8 : ℝ) * z^2 * (y - z)^1 * (x - y)^3 + (20 : ℝ) * z^1 * (y - z)^5 + (50 : ℝ) * z^1 * (y - z)^4 * (x - y)^1 + (40 : ℝ) * z^1 * (y - z)^3 * (x - y)^2 + (10 : ℝ) * z^1 * (y - z)^2 * (x - y)^3 + (4 : ℝ) * (y - z)^6 + (12 : ℝ) * (y - z)^5 * (x - y)^1 + (12 : ℝ) * (y - z)^4 * (x - y)^2 + (4 : ℝ) * (y - z)^3 * (x - y)^3 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (4*x^3*y^3 - 2*x^3*y^2*z + 2*x^3*z^3 - 2*x^2*y^3*z - 3*x^2*y^2*z^2 - x*y^3*z^2 - x*y^2*z^3 + 3*y^3*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 3 * y * z / x ^ 2 + 2 * x * z / y ^ 2 + 4 * x * y / z ^ 2 ≥ 3 + y / x + z / x + 2 * x / z + 2 * y / z) := @solution
#print axioms solution
