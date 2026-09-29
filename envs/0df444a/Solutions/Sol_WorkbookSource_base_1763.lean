-- Prove2me | solution 1 for WorkbookSource.base_1763
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:47:39.518976+00:00
-- url     : https://prove2.me/submissions/2378d973-a3bd-4da6-ac3f-67136117459e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (z^4 + x*y^3 + 2*x*z^3 + x^3*z + y*z^3 + 2*z^2*x^2 + x*y*z^2 - 3*x*y^2*z - z*x^2*y) * (x - y) * (x - z) + x * (y^3 + z^3 + 2*x*y^2 - x^2*y + z^2*x - y^2*z + 2*x*y*z) * (y - z)^2 ≥ 0  := by
  have hp : 0 ≤ (x^5*z - 2*x^4*y*z + x^4*z^2 + x^2*y^4 + x*y^5 - 2*x*y^4*z - 2*x*y*z^4 + y^2*z^4 + y*z^5) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (y - x) := by linarith
        have hdiff2 : 0 ≤ (z - y) := by linarith
        have hpos : 0 ≤ (5 : ℝ) * x^4 * (y - x)^2 + (5 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (5 : ℝ) * x^4 * (z - y)^2 + (14 : ℝ) * x^3 * (y - x)^3 + (30 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (28 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (6 : ℝ) * x^3 * (z - y)^3 + (16 : ℝ) * x^2 * (y - x)^4 + (50 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (60 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (26 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (4 : ℝ) * x^2 * (z - y)^4 + (9 : ℝ) * x^1 * (y - x)^5 + (35 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (52 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (34 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (10 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (1 : ℝ) * x^1 * (z - y)^5 + (2 : ℝ) * (y - x)^6 + (9 : ℝ) * (y - x)^5 * (z - y)^1 + (16 : ℝ) * (y - x)^4 * (z - y)^2 + (14 : ℝ) * (y - x)^3 * (z - y)^3 + (6 : ℝ) * (y - x)^2 * (z - y)^4 + (1 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - x) := by linarith
          have hdiff2 : 0 ≤ (y - z) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * x^4 * (z - x)^2 + (5 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (5 : ℝ) * x^4 * (y - z)^2 + (14 : ℝ) * x^3 * (z - x)^3 + (12 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (10 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (6 : ℝ) * x^3 * (y - z)^3 + (16 : ℝ) * x^2 * (z - x)^4 + (14 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (6 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (8 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (4 : ℝ) * x^2 * (y - z)^4 + (9 : ℝ) * x^1 * (z - x)^5 + (10 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (2 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (2 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (3 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (1 : ℝ) * x^1 * (y - z)^5 + (2 : ℝ) * (z - x)^6 + (3 : ℝ) * (z - x)^5 * (y - z)^1 + (1 : ℝ) * (z - x)^4 * (y - z)^2 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (x - z) := by linarith
          have hdiff2 : 0 ≤ (y - x) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * z^4 * (x - z)^2 + (5 : ℝ) * z^4 * (x - z)^1 * (y - x)^1 + (5 : ℝ) * z^4 * (y - x)^2 + (14 : ℝ) * z^3 * (x - z)^3 + (30 : ℝ) * z^3 * (x - z)^2 * (y - x)^1 + (28 : ℝ) * z^3 * (x - z)^1 * (y - x)^2 + (6 : ℝ) * z^3 * (y - x)^3 + (16 : ℝ) * z^2 * (x - z)^4 + (50 : ℝ) * z^2 * (x - z)^3 * (y - x)^1 + (60 : ℝ) * z^2 * (x - z)^2 * (y - x)^2 + (26 : ℝ) * z^2 * (x - z)^1 * (y - x)^3 + (4 : ℝ) * z^2 * (y - x)^4 + (9 : ℝ) * z^1 * (x - z)^5 + (35 : ℝ) * z^1 * (x - z)^4 * (y - x)^1 + (52 : ℝ) * z^1 * (x - z)^3 * (y - x)^2 + (34 : ℝ) * z^1 * (x - z)^2 * (y - x)^3 + (10 : ℝ) * z^1 * (x - z)^1 * (y - x)^4 + (1 : ℝ) * z^1 * (y - x)^5 + (2 : ℝ) * (x - z)^6 + (9 : ℝ) * (x - z)^5 * (y - x)^1 + (16 : ℝ) * (x - z)^4 * (y - x)^2 + (14 : ℝ) * (x - z)^3 * (y - x)^3 + (6 : ℝ) * (x - z)^2 * (y - x)^4 + (1 : ℝ) * (x - z)^1 * (y - x)^5 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (x - y) := by linarith
        have hdiff2 : 0 ≤ (z - x) := by linarith
        have hpos : 0 ≤ (5 : ℝ) * y^4 * (x - y)^2 + (5 : ℝ) * y^4 * (x - y)^1 * (z - x)^1 + (5 : ℝ) * y^4 * (z - x)^2 + (14 : ℝ) * y^3 * (x - y)^3 + (12 : ℝ) * y^3 * (x - y)^2 * (z - x)^1 + (10 : ℝ) * y^3 * (x - y)^1 * (z - x)^2 + (6 : ℝ) * y^3 * (z - x)^3 + (16 : ℝ) * y^2 * (x - y)^4 + (14 : ℝ) * y^2 * (x - y)^3 * (z - x)^1 + (6 : ℝ) * y^2 * (x - y)^2 * (z - x)^2 + (8 : ℝ) * y^2 * (x - y)^1 * (z - x)^3 + (4 : ℝ) * y^2 * (z - x)^4 + (9 : ℝ) * y^1 * (x - y)^5 + (10 : ℝ) * y^1 * (x - y)^4 * (z - x)^1 + (2 : ℝ) * y^1 * (x - y)^3 * (z - x)^2 + (2 : ℝ) * y^1 * (x - y)^2 * (z - x)^3 + (3 : ℝ) * y^1 * (x - y)^1 * (z - x)^4 + (1 : ℝ) * y^1 * (z - x)^5 + (2 : ℝ) * (x - y)^6 + (3 : ℝ) * (x - y)^5 * (z - x)^1 + (1 : ℝ) * (x - y)^4 * (z - x)^2 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - y) := by linarith
          have hdiff2 : 0 ≤ (x - z) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * y^4 * (z - y)^2 + (5 : ℝ) * y^4 * (z - y)^1 * (x - z)^1 + (5 : ℝ) * y^4 * (x - z)^2 + (14 : ℝ) * y^3 * (z - y)^3 + (30 : ℝ) * y^3 * (z - y)^2 * (x - z)^1 + (28 : ℝ) * y^3 * (z - y)^1 * (x - z)^2 + (6 : ℝ) * y^3 * (x - z)^3 + (16 : ℝ) * y^2 * (z - y)^4 + (50 : ℝ) * y^2 * (z - y)^3 * (x - z)^1 + (60 : ℝ) * y^2 * (z - y)^2 * (x - z)^2 + (26 : ℝ) * y^2 * (z - y)^1 * (x - z)^3 + (4 : ℝ) * y^2 * (x - z)^4 + (9 : ℝ) * y^1 * (z - y)^5 + (35 : ℝ) * y^1 * (z - y)^4 * (x - z)^1 + (52 : ℝ) * y^1 * (z - y)^3 * (x - z)^2 + (34 : ℝ) * y^1 * (z - y)^2 * (x - z)^3 + (10 : ℝ) * y^1 * (z - y)^1 * (x - z)^4 + (1 : ℝ) * y^1 * (x - z)^5 + (2 : ℝ) * (z - y)^6 + (9 : ℝ) * (z - y)^5 * (x - z)^1 + (16 : ℝ) * (z - y)^4 * (x - z)^2 + (14 : ℝ) * (z - y)^3 * (x - z)^3 + (6 : ℝ) * (z - y)^2 * (x - z)^4 + (1 : ℝ) * (z - y)^1 * (x - z)^5 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (y - z) := by linarith
          have hdiff2 : 0 ≤ (x - y) := by linarith
          have hpos : 0 ≤ (5 : ℝ) * z^4 * (y - z)^2 + (5 : ℝ) * z^4 * (y - z)^1 * (x - y)^1 + (5 : ℝ) * z^4 * (x - y)^2 + (14 : ℝ) * z^3 * (y - z)^3 + (12 : ℝ) * z^3 * (y - z)^2 * (x - y)^1 + (10 : ℝ) * z^3 * (y - z)^1 * (x - y)^2 + (6 : ℝ) * z^3 * (x - y)^3 + (16 : ℝ) * z^2 * (y - z)^4 + (14 : ℝ) * z^2 * (y - z)^3 * (x - y)^1 + (6 : ℝ) * z^2 * (y - z)^2 * (x - y)^2 + (8 : ℝ) * z^2 * (y - z)^1 * (x - y)^3 + (4 : ℝ) * z^2 * (x - y)^4 + (9 : ℝ) * z^1 * (y - z)^5 + (10 : ℝ) * z^1 * (y - z)^4 * (x - y)^1 + (2 : ℝ) * z^1 * (y - z)^3 * (x - y)^2 + (2 : ℝ) * z^1 * (y - z)^2 * (x - y)^3 + (3 : ℝ) * z^1 * (y - z)^1 * (x - y)^4 + (1 : ℝ) * z^1 * (x - y)^5 + (2 : ℝ) * (y - z)^6 + (3 : ℝ) * (y - z)^5 * (x - y)^1 + (1 : ℝ) * (y - z)^4 * (x - y)^2 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (z^4 + x*y^3 + 2*x*z^3 + x^3*z + y*z^3 + 2*z^2*x^2 + x*y*z^2 - 3*x*y^2*z - z*x^2*y) * (x - y) * (x - z) + x * (y^3 + z^3 + 2*x*y^2 - x^2*y + z^2*x - y^2*z + 2*x*y*z) * (y - z)^2 ≥ 0) := @solution
#print axioms solution
