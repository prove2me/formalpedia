-- Prove2me | solution 1 for WorkbookSource.base_9974
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:39.518114+00:00
-- url     : https://prove2.me/submissions/ba9f89f1-757f-4801-b0fe-ee3498662f40

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x + y + z) * (x ^ 3 * y + z * y ^ 3 + x * z ^ 3) ≥ (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) * (x * y + y * z + x * z)  := by
  have hp : 0 ≤ (x^4*y - x^2*y^2*z - x^2*y*z^2 - x*y^2*z^2 + x*z^4 + y^4*z) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (y - x) := by linarith
        have hdiff2 : 0 ≤ (z - y) := by linarith
        have hpos : 0 ≤ (4 : ℝ) * x^3 * (y - x)^2 + (4 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (4 : ℝ) * x^3 * (z - y)^2 + (8 : ℝ) * x^2 * (y - x)^3 + (9 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (9 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (4 : ℝ) * x^2 * (z - y)^3 + (5 : ℝ) * x^1 * (y - x)^4 + (6 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (5 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (4 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (1 : ℝ) * x^1 * (z - y)^4 + (1 : ℝ) * (y - x)^5 + (1 : ℝ) * (y - x)^4 * (z - y)^1 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - x) := by linarith
          have hdiff2 : 0 ≤ (y - z) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * x^3 * (z - x)^2 + (4 : ℝ) * x^3 * (z - x)^1 * (y - z)^1 + (4 : ℝ) * x^3 * (y - z)^2 + (8 : ℝ) * x^2 * (z - x)^3 + (15 : ℝ) * x^2 * (z - x)^2 * (y - z)^1 + (15 : ℝ) * x^2 * (z - x)^1 * (y - z)^2 + (4 : ℝ) * x^2 * (y - z)^3 + (5 : ℝ) * x^1 * (z - x)^4 + (14 : ℝ) * x^1 * (z - x)^3 * (y - z)^1 + (17 : ℝ) * x^1 * (z - x)^2 * (y - z)^2 + (8 : ℝ) * x^1 * (z - x)^1 * (y - z)^3 + (1 : ℝ) * x^1 * (y - z)^4 + (1 : ℝ) * (z - x)^5 + (4 : ℝ) * (z - x)^4 * (y - z)^1 + (6 : ℝ) * (z - x)^3 * (y - z)^2 + (4 : ℝ) * (z - x)^2 * (y - z)^3 + (1 : ℝ) * (z - x)^1 * (y - z)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (x - z) := by linarith
          have hdiff2 : 0 ≤ (y - x) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * z^3 * (x - z)^2 + (4 : ℝ) * z^3 * (x - z)^1 * (y - x)^1 + (4 : ℝ) * z^3 * (y - x)^2 + (8 : ℝ) * z^2 * (x - z)^3 + (9 : ℝ) * z^2 * (x - z)^2 * (y - x)^1 + (9 : ℝ) * z^2 * (x - z)^1 * (y - x)^2 + (4 : ℝ) * z^2 * (y - x)^3 + (5 : ℝ) * z^1 * (x - z)^4 + (6 : ℝ) * z^1 * (x - z)^3 * (y - x)^1 + (5 : ℝ) * z^1 * (x - z)^2 * (y - x)^2 + (4 : ℝ) * z^1 * (x - z)^1 * (y - x)^3 + (1 : ℝ) * z^1 * (y - x)^4 + (1 : ℝ) * (x - z)^5 + (1 : ℝ) * (x - z)^4 * (y - x)^1 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (x - y) := by linarith
        have hdiff2 : 0 ≤ (z - x) := by linarith
        have hpos : 0 ≤ (4 : ℝ) * y^3 * (x - y)^2 + (4 : ℝ) * y^3 * (x - y)^1 * (z - x)^1 + (4 : ℝ) * y^3 * (z - x)^2 + (8 : ℝ) * y^2 * (x - y)^3 + (15 : ℝ) * y^2 * (x - y)^2 * (z - x)^1 + (15 : ℝ) * y^2 * (x - y)^1 * (z - x)^2 + (4 : ℝ) * y^2 * (z - x)^3 + (5 : ℝ) * y^1 * (x - y)^4 + (14 : ℝ) * y^1 * (x - y)^3 * (z - x)^1 + (17 : ℝ) * y^1 * (x - y)^2 * (z - x)^2 + (8 : ℝ) * y^1 * (x - y)^1 * (z - x)^3 + (1 : ℝ) * y^1 * (z - x)^4 + (1 : ℝ) * (x - y)^5 + (4 : ℝ) * (x - y)^4 * (z - x)^1 + (6 : ℝ) * (x - y)^3 * (z - x)^2 + (4 : ℝ) * (x - y)^2 * (z - x)^3 + (1 : ℝ) * (x - y)^1 * (z - x)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - y) := by linarith
          have hdiff2 : 0 ≤ (x - z) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * y^3 * (z - y)^2 + (4 : ℝ) * y^3 * (z - y)^1 * (x - z)^1 + (4 : ℝ) * y^3 * (x - z)^2 + (8 : ℝ) * y^2 * (z - y)^3 + (9 : ℝ) * y^2 * (z - y)^2 * (x - z)^1 + (9 : ℝ) * y^2 * (z - y)^1 * (x - z)^2 + (4 : ℝ) * y^2 * (x - z)^3 + (5 : ℝ) * y^1 * (z - y)^4 + (6 : ℝ) * y^1 * (z - y)^3 * (x - z)^1 + (5 : ℝ) * y^1 * (z - y)^2 * (x - z)^2 + (4 : ℝ) * y^1 * (z - y)^1 * (x - z)^3 + (1 : ℝ) * y^1 * (x - z)^4 + (1 : ℝ) * (z - y)^5 + (1 : ℝ) * (z - y)^4 * (x - z)^1 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (y - z) := by linarith
          have hdiff2 : 0 ≤ (x - y) := by linarith
          have hpos : 0 ≤ (4 : ℝ) * z^3 * (y - z)^2 + (4 : ℝ) * z^3 * (y - z)^1 * (x - y)^1 + (4 : ℝ) * z^3 * (x - y)^2 + (8 : ℝ) * z^2 * (y - z)^3 + (15 : ℝ) * z^2 * (y - z)^2 * (x - y)^1 + (15 : ℝ) * z^2 * (y - z)^1 * (x - y)^2 + (4 : ℝ) * z^2 * (x - y)^3 + (5 : ℝ) * z^1 * (y - z)^4 + (14 : ℝ) * z^1 * (y - z)^3 * (x - y)^1 + (17 : ℝ) * z^1 * (y - z)^2 * (x - y)^2 + (8 : ℝ) * z^1 * (y - z)^1 * (x - y)^3 + (1 : ℝ) * z^1 * (x - y)^4 + (1 : ℝ) * (y - z)^5 + (4 : ℝ) * (y - z)^4 * (x - y)^1 + (6 : ℝ) * (y - z)^3 * (x - y)^2 + (4 : ℝ) * (y - z)^2 * (x - y)^3 + (1 : ℝ) * (y - z)^1 * (x - y)^4 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0), (x + y + z) * (x ^ 3 * y + z * y ^ 3 + x * z ^ 3) ≥ (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) * (x * y + y * z + x * z)) := @solution
#print axioms solution
