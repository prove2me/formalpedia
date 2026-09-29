-- Prove2me | solution 1 for WorkbookSource.base_8206
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:33.730043+00:00
-- url     : https://prove2.me/submissions/788b70d2-4a03-43a3-be8d-be44e61e7c44

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^3 * (y^2 + z^2)^2 + y^3 * (z^2 + x^2)^2 + z^3 * (x^2 + y^2)^2 ≥ x * y * z * (x * y * (x + y)^2 + y * z * (y + z)^2 + z * x * (z + x)^2)  := by
  have hp : 0 ≤ (x^4*y^3 - x^4*y^2*z - x^4*y*z^2 + x^4*z^3 + x^3*y^4 - 2*x^3*y^3*z + 2*x^3*y^2*z^2 - 2*x^3*y*z^3 + x^3*z^4 - x^2*y^4*z + 2*x^2*y^3*z^2 + 2*x^2*y^2*z^3 - x^2*y*z^4 - x*y^4*z^2 - 2*x*y^3*z^3 - x*y^2*z^4 + y^4*z^3 + y^3*z^4) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (y - x) := by linarith
        have hdiff2 : 0 ≤ (z - y) := by linarith
        have hpos : 0 ≤ (2 : ℝ) * x^5 * (y - x)^2 + (2 : ℝ) * x^5 * (y - x)^1 * (z - y)^1 + (2 : ℝ) * x^5 * (z - y)^2 + (10 : ℝ) * x^4 * (y - x)^3 + (15 : ℝ) * x^4 * (y - x)^2 * (z - y)^1 + (5 : ℝ) * x^4 * (y - x)^1 * (z - y)^2 + (20 : ℝ) * x^3 * (y - x)^4 + (40 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (20 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (20 : ℝ) * x^2 * (y - x)^5 + (50 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (40 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (10 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (10 : ℝ) * x^1 * (y - x)^6 + (30 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (32 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (14 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (2 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (2 : ℝ) * (y - x)^7 + (7 : ℝ) * (y - x)^6 * (z - y)^1 + (9 : ℝ) * (y - x)^5 * (z - y)^2 + (5 : ℝ) * (y - x)^4 * (z - y)^3 + (1 : ℝ) * (y - x)^3 * (z - y)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - x) := by linarith
          have hdiff2 : 0 ≤ (y - z) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * x^5 * (z - x)^2 + (2 : ℝ) * x^5 * (z - x)^1 * (y - z)^1 + (2 : ℝ) * x^5 * (y - z)^2 + (10 : ℝ) * x^4 * (z - x)^3 + (15 : ℝ) * x^4 * (z - x)^2 * (y - z)^1 + (5 : ℝ) * x^4 * (z - x)^1 * (y - z)^2 + (20 : ℝ) * x^3 * (z - x)^4 + (40 : ℝ) * x^3 * (z - x)^3 * (y - z)^1 + (20 : ℝ) * x^3 * (z - x)^2 * (y - z)^2 + (20 : ℝ) * x^2 * (z - x)^5 + (50 : ℝ) * x^2 * (z - x)^4 * (y - z)^1 + (40 : ℝ) * x^2 * (z - x)^3 * (y - z)^2 + (10 : ℝ) * x^2 * (z - x)^2 * (y - z)^3 + (10 : ℝ) * x^1 * (z - x)^6 + (30 : ℝ) * x^1 * (z - x)^5 * (y - z)^1 + (32 : ℝ) * x^1 * (z - x)^4 * (y - z)^2 + (14 : ℝ) * x^1 * (z - x)^3 * (y - z)^3 + (2 : ℝ) * x^1 * (z - x)^2 * (y - z)^4 + (2 : ℝ) * (z - x)^7 + (7 : ℝ) * (z - x)^6 * (y - z)^1 + (9 : ℝ) * (z - x)^5 * (y - z)^2 + (5 : ℝ) * (z - x)^4 * (y - z)^3 + (1 : ℝ) * (z - x)^3 * (y - z)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (x - z) := by linarith
          have hdiff2 : 0 ≤ (y - x) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * z^5 * (x - z)^2 + (2 : ℝ) * z^5 * (x - z)^1 * (y - x)^1 + (2 : ℝ) * z^5 * (y - x)^2 + (10 : ℝ) * z^4 * (x - z)^3 + (15 : ℝ) * z^4 * (x - z)^2 * (y - x)^1 + (5 : ℝ) * z^4 * (x - z)^1 * (y - x)^2 + (20 : ℝ) * z^3 * (x - z)^4 + (40 : ℝ) * z^3 * (x - z)^3 * (y - x)^1 + (20 : ℝ) * z^3 * (x - z)^2 * (y - x)^2 + (20 : ℝ) * z^2 * (x - z)^5 + (50 : ℝ) * z^2 * (x - z)^4 * (y - x)^1 + (40 : ℝ) * z^2 * (x - z)^3 * (y - x)^2 + (10 : ℝ) * z^2 * (x - z)^2 * (y - x)^3 + (10 : ℝ) * z^1 * (x - z)^6 + (30 : ℝ) * z^1 * (x - z)^5 * (y - x)^1 + (32 : ℝ) * z^1 * (x - z)^4 * (y - x)^2 + (14 : ℝ) * z^1 * (x - z)^3 * (y - x)^3 + (2 : ℝ) * z^1 * (x - z)^2 * (y - x)^4 + (2 : ℝ) * (x - z)^7 + (7 : ℝ) * (x - z)^6 * (y - x)^1 + (9 : ℝ) * (x - z)^5 * (y - x)^2 + (5 : ℝ) * (x - z)^4 * (y - x)^3 + (1 : ℝ) * (x - z)^3 * (y - x)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (x - y) := by linarith
        have hdiff2 : 0 ≤ (z - x) := by linarith
        have hpos : 0 ≤ (2 : ℝ) * y^5 * (x - y)^2 + (2 : ℝ) * y^5 * (x - y)^1 * (z - x)^1 + (2 : ℝ) * y^5 * (z - x)^2 + (10 : ℝ) * y^4 * (x - y)^3 + (15 : ℝ) * y^4 * (x - y)^2 * (z - x)^1 + (5 : ℝ) * y^4 * (x - y)^1 * (z - x)^2 + (20 : ℝ) * y^3 * (x - y)^4 + (40 : ℝ) * y^3 * (x - y)^3 * (z - x)^1 + (20 : ℝ) * y^3 * (x - y)^2 * (z - x)^2 + (20 : ℝ) * y^2 * (x - y)^5 + (50 : ℝ) * y^2 * (x - y)^4 * (z - x)^1 + (40 : ℝ) * y^2 * (x - y)^3 * (z - x)^2 + (10 : ℝ) * y^2 * (x - y)^2 * (z - x)^3 + (10 : ℝ) * y^1 * (x - y)^6 + (30 : ℝ) * y^1 * (x - y)^5 * (z - x)^1 + (32 : ℝ) * y^1 * (x - y)^4 * (z - x)^2 + (14 : ℝ) * y^1 * (x - y)^3 * (z - x)^3 + (2 : ℝ) * y^1 * (x - y)^2 * (z - x)^4 + (2 : ℝ) * (x - y)^7 + (7 : ℝ) * (x - y)^6 * (z - x)^1 + (9 : ℝ) * (x - y)^5 * (z - x)^2 + (5 : ℝ) * (x - y)^4 * (z - x)^3 + (1 : ℝ) * (x - y)^3 * (z - x)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - y) := by linarith
          have hdiff2 : 0 ≤ (x - z) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * y^5 * (z - y)^2 + (2 : ℝ) * y^5 * (z - y)^1 * (x - z)^1 + (2 : ℝ) * y^5 * (x - z)^2 + (10 : ℝ) * y^4 * (z - y)^3 + (15 : ℝ) * y^4 * (z - y)^2 * (x - z)^1 + (5 : ℝ) * y^4 * (z - y)^1 * (x - z)^2 + (20 : ℝ) * y^3 * (z - y)^4 + (40 : ℝ) * y^3 * (z - y)^3 * (x - z)^1 + (20 : ℝ) * y^3 * (z - y)^2 * (x - z)^2 + (20 : ℝ) * y^2 * (z - y)^5 + (50 : ℝ) * y^2 * (z - y)^4 * (x - z)^1 + (40 : ℝ) * y^2 * (z - y)^3 * (x - z)^2 + (10 : ℝ) * y^2 * (z - y)^2 * (x - z)^3 + (10 : ℝ) * y^1 * (z - y)^6 + (30 : ℝ) * y^1 * (z - y)^5 * (x - z)^1 + (32 : ℝ) * y^1 * (z - y)^4 * (x - z)^2 + (14 : ℝ) * y^1 * (z - y)^3 * (x - z)^3 + (2 : ℝ) * y^1 * (z - y)^2 * (x - z)^4 + (2 : ℝ) * (z - y)^7 + (7 : ℝ) * (z - y)^6 * (x - z)^1 + (9 : ℝ) * (z - y)^5 * (x - z)^2 + (5 : ℝ) * (z - y)^4 * (x - z)^3 + (1 : ℝ) * (z - y)^3 * (x - z)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (y - z) := by linarith
          have hdiff2 : 0 ≤ (x - y) := by linarith
          have hpos : 0 ≤ (2 : ℝ) * z^5 * (y - z)^2 + (2 : ℝ) * z^5 * (y - z)^1 * (x - y)^1 + (2 : ℝ) * z^5 * (x - y)^2 + (10 : ℝ) * z^4 * (y - z)^3 + (15 : ℝ) * z^4 * (y - z)^2 * (x - y)^1 + (5 : ℝ) * z^4 * (y - z)^1 * (x - y)^2 + (20 : ℝ) * z^3 * (y - z)^4 + (40 : ℝ) * z^3 * (y - z)^3 * (x - y)^1 + (20 : ℝ) * z^3 * (y - z)^2 * (x - y)^2 + (20 : ℝ) * z^2 * (y - z)^5 + (50 : ℝ) * z^2 * (y - z)^4 * (x - y)^1 + (40 : ℝ) * z^2 * (y - z)^3 * (x - y)^2 + (10 : ℝ) * z^2 * (y - z)^2 * (x - y)^3 + (10 : ℝ) * z^1 * (y - z)^6 + (30 : ℝ) * z^1 * (y - z)^5 * (x - y)^1 + (32 : ℝ) * z^1 * (y - z)^4 * (x - y)^2 + (14 : ℝ) * z^1 * (y - z)^3 * (x - y)^3 + (2 : ℝ) * z^1 * (y - z)^2 * (x - y)^4 + (2 : ℝ) * (y - z)^7 + (7 : ℝ) * (y - z)^6 * (x - y)^1 + (9 : ℝ) * (y - z)^5 * (x - y)^2 + (5 : ℝ) * (y - z)^4 * (x - y)^3 + (1 : ℝ) * (y - z)^3 * (x - y)^4 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x^3 * (y^2 + z^2)^2 + y^3 * (z^2 + x^2)^2 + z^3 * (x^2 + y^2)^2 ≥ x * y * z * (x * y * (x + y)^2 + y * z * (y + z)^2 + z * x * (z + x)^2)) := @solution
#print axioms solution
