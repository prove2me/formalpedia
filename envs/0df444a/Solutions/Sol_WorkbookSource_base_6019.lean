-- Prove2me | solution 1 for WorkbookSource.base_6019
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:31.046671+00:00
-- url     : https://prove2.me/submissions/4cb5c6a3-cf97-41ab-9949-0a6026845e06

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^3 + y^3 + z^3 + x * y * z)^2 ≥ 2 * (x^2 + y^2) * (x^2 + z^2) * (y^2 + z^2)  := by
  have hp : 0 ≤ (x^6 - 2*x^4*y^2 + 2*x^4*y*z - 2*x^4*z^2 + 2*x^3*y^3 + 2*x^3*z^3 - 2*x^2*y^4 - 3*x^2*y^2*z^2 - 2*x^2*z^4 + 2*x*y^4*z + 2*x*y*z^4 + y^6 - 2*y^4*z^2 + 2*y^3*z^3 - 2*y^2*z^4 + z^6) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (y - x) := by linarith
        have hdiff2 : 0 ≤ (z - y) := by linarith
        have hpos : 0 ≤ (8 : ℝ) * x^4 * (y - x)^2 + (8 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (8 : ℝ) * x^4 * (z - y)^2 + (16 : ℝ) * x^3 * (y - x)^3 + (24 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (40 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (16 : ℝ) * x^3 * (z - y)^3 + (13 : ℝ) * x^2 * (y - x)^4 + (26 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (63 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (50 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (13 : ℝ) * x^2 * (z - y)^4 + (4 : ℝ) * x^1 * (y - x)^5 + (10 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (40 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (50 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (28 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (6 : ℝ) * x^1 * (z - y)^5 + (7 : ℝ) * (y - x)^4 * (z - y)^2 + (14 : ℝ) * (y - x)^3 * (z - y)^3 + (13 : ℝ) * (y - x)^2 * (z - y)^4 + (6 : ℝ) * (y - x)^1 * (z - y)^5 + (1 : ℝ) * (z - y)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - x) := by linarith
          have hdiff2 : 0 ≤ (y - z) := by linarith
          have hpos : 0 ≤ (8 : ℝ) * x^4 * (z - x)^2 + (8 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (8 : ℝ) * x^4 * (y - z)^2 + (16 : ℝ) * x^3 * (z - x)^3 + (24 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (40 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (16 : ℝ) * x^3 * (y - z)^3 + (13 : ℝ) * x^2 * (z - x)^4 + (26 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (63 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (50 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (13 : ℝ) * x^2 * (y - z)^4 + (4 : ℝ) * x^1 * (z - x)^5 + (10 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (40 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (50 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (28 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (6 : ℝ) * x^1 * (y - z)^5 + (7 : ℝ) * (z - x)^4 * (y - z)^2 + (14 : ℝ) * (z - x)^3 * (y - z)^3 + (13 : ℝ) * (z - x)^2 * (y - z)^4 + (6 : ℝ) * (z - x)^1 * (y - z)^5 + (1 : ℝ) * (y - z)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (x - z) := by linarith
          have hdiff2 : 0 ≤ (y - x) := by linarith
          have hpos : 0 ≤ (8 : ℝ) * z^4 * (x - z)^2 + (8 : ℝ) * z^4 * (x - z)^1 * (y - x)^1 + (8 : ℝ) * z^4 * (y - x)^2 + (16 : ℝ) * z^3 * (x - z)^3 + (24 : ℝ) * z^3 * (x - z)^2 * (y - x)^1 + (40 : ℝ) * z^3 * (x - z)^1 * (y - x)^2 + (16 : ℝ) * z^3 * (y - x)^3 + (13 : ℝ) * z^2 * (x - z)^4 + (26 : ℝ) * z^2 * (x - z)^3 * (y - x)^1 + (63 : ℝ) * z^2 * (x - z)^2 * (y - x)^2 + (50 : ℝ) * z^2 * (x - z)^1 * (y - x)^3 + (13 : ℝ) * z^2 * (y - x)^4 + (4 : ℝ) * z^1 * (x - z)^5 + (10 : ℝ) * z^1 * (x - z)^4 * (y - x)^1 + (40 : ℝ) * z^1 * (x - z)^3 * (y - x)^2 + (50 : ℝ) * z^1 * (x - z)^2 * (y - x)^3 + (28 : ℝ) * z^1 * (x - z)^1 * (y - x)^4 + (6 : ℝ) * z^1 * (y - x)^5 + (7 : ℝ) * (x - z)^4 * (y - x)^2 + (14 : ℝ) * (x - z)^3 * (y - x)^3 + (13 : ℝ) * (x - z)^2 * (y - x)^4 + (6 : ℝ) * (x - z)^1 * (y - x)^5 + (1 : ℝ) * (y - x)^6 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (x - y) := by linarith
        have hdiff2 : 0 ≤ (z - x) := by linarith
        have hpos : 0 ≤ (8 : ℝ) * y^4 * (x - y)^2 + (8 : ℝ) * y^4 * (x - y)^1 * (z - x)^1 + (8 : ℝ) * y^4 * (z - x)^2 + (16 : ℝ) * y^3 * (x - y)^3 + (24 : ℝ) * y^3 * (x - y)^2 * (z - x)^1 + (40 : ℝ) * y^3 * (x - y)^1 * (z - x)^2 + (16 : ℝ) * y^3 * (z - x)^3 + (13 : ℝ) * y^2 * (x - y)^4 + (26 : ℝ) * y^2 * (x - y)^3 * (z - x)^1 + (63 : ℝ) * y^2 * (x - y)^2 * (z - x)^2 + (50 : ℝ) * y^2 * (x - y)^1 * (z - x)^3 + (13 : ℝ) * y^2 * (z - x)^4 + (4 : ℝ) * y^1 * (x - y)^5 + (10 : ℝ) * y^1 * (x - y)^4 * (z - x)^1 + (40 : ℝ) * y^1 * (x - y)^3 * (z - x)^2 + (50 : ℝ) * y^1 * (x - y)^2 * (z - x)^3 + (28 : ℝ) * y^1 * (x - y)^1 * (z - x)^4 + (6 : ℝ) * y^1 * (z - x)^5 + (7 : ℝ) * (x - y)^4 * (z - x)^2 + (14 : ℝ) * (x - y)^3 * (z - x)^3 + (13 : ℝ) * (x - y)^2 * (z - x)^4 + (6 : ℝ) * (x - y)^1 * (z - x)^5 + (1 : ℝ) * (z - x)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - y) := by linarith
          have hdiff2 : 0 ≤ (x - z) := by linarith
          have hpos : 0 ≤ (8 : ℝ) * y^4 * (z - y)^2 + (8 : ℝ) * y^4 * (z - y)^1 * (x - z)^1 + (8 : ℝ) * y^4 * (x - z)^2 + (16 : ℝ) * y^3 * (z - y)^3 + (24 : ℝ) * y^3 * (z - y)^2 * (x - z)^1 + (40 : ℝ) * y^3 * (z - y)^1 * (x - z)^2 + (16 : ℝ) * y^3 * (x - z)^3 + (13 : ℝ) * y^2 * (z - y)^4 + (26 : ℝ) * y^2 * (z - y)^3 * (x - z)^1 + (63 : ℝ) * y^2 * (z - y)^2 * (x - z)^2 + (50 : ℝ) * y^2 * (z - y)^1 * (x - z)^3 + (13 : ℝ) * y^2 * (x - z)^4 + (4 : ℝ) * y^1 * (z - y)^5 + (10 : ℝ) * y^1 * (z - y)^4 * (x - z)^1 + (40 : ℝ) * y^1 * (z - y)^3 * (x - z)^2 + (50 : ℝ) * y^1 * (z - y)^2 * (x - z)^3 + (28 : ℝ) * y^1 * (z - y)^1 * (x - z)^4 + (6 : ℝ) * y^1 * (x - z)^5 + (7 : ℝ) * (z - y)^4 * (x - z)^2 + (14 : ℝ) * (z - y)^3 * (x - z)^3 + (13 : ℝ) * (z - y)^2 * (x - z)^4 + (6 : ℝ) * (z - y)^1 * (x - z)^5 + (1 : ℝ) * (x - z)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (y - z) := by linarith
          have hdiff2 : 0 ≤ (x - y) := by linarith
          have hpos : 0 ≤ (8 : ℝ) * z^4 * (y - z)^2 + (8 : ℝ) * z^4 * (y - z)^1 * (x - y)^1 + (8 : ℝ) * z^4 * (x - y)^2 + (16 : ℝ) * z^3 * (y - z)^3 + (24 : ℝ) * z^3 * (y - z)^2 * (x - y)^1 + (40 : ℝ) * z^3 * (y - z)^1 * (x - y)^2 + (16 : ℝ) * z^3 * (x - y)^3 + (13 : ℝ) * z^2 * (y - z)^4 + (26 : ℝ) * z^2 * (y - z)^3 * (x - y)^1 + (63 : ℝ) * z^2 * (y - z)^2 * (x - y)^2 + (50 : ℝ) * z^2 * (y - z)^1 * (x - y)^3 + (13 : ℝ) * z^2 * (x - y)^4 + (4 : ℝ) * z^1 * (y - z)^5 + (10 : ℝ) * z^1 * (y - z)^4 * (x - y)^1 + (40 : ℝ) * z^1 * (y - z)^3 * (x - y)^2 + (50 : ℝ) * z^1 * (y - z)^2 * (x - y)^3 + (28 : ℝ) * z^1 * (y - z)^1 * (x - y)^4 + (6 : ℝ) * z^1 * (x - y)^5 + (7 : ℝ) * (y - z)^4 * (x - y)^2 + (14 : ℝ) * (y - z)^3 * (x - y)^3 + (13 : ℝ) * (y - z)^2 * (x - y)^4 + (6 : ℝ) * (y - z)^1 * (x - y)^5 + (1 : ℝ) * (x - y)^6 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x^3 + y^3 + z^3 + x * y * z)^2 ≥ 2 * (x^2 + y^2) * (x^2 + z^2) * (y^2 + z^2)) := @solution
#print axioms solution
