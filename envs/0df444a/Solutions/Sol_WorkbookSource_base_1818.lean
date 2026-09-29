-- Prove2me | solution 1 for WorkbookSource.base_1818
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:47:40.205623+00:00
-- url     : https://prove2.me/submissions/13678ede-670a-4985-ad57-cf63021c6706

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 4 * (x ^ 6 + y ^ 6 + z ^ 6) + 27 * x ^ 2 * y ^ 2 * z ^ 2 ≥ 12 * (x ^ 4 * y * z + y ^ 4 * z * x + z ^ 4 * x * y) + (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3)  := by
  have hp : 0 ≤ (4*x^6 - 12*x^4*y*z - x^3*y^3 - x^3*z^3 + 27*x^2*y^2*z^2 - 12*x*y^4*z - 12*x*y*z^4 + 4*y^6 - y^3*z^3 + 4*z^6) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (y - x) := by linarith
        have hdiff2 : 0 ≤ (z - y) := by linarith
        have hpos : 0 ≤ (9 : ℝ) * x^4 * (y - x)^2 + (9 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (9 : ℝ) * x^4 * (z - y)^2 + (6 : ℝ) * x^3 * (y - x)^3 + (9 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (63 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (30 : ℝ) * x^3 * (z - y)^3 + (12 : ℝ) * x^2 * (y - x)^4 + (24 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (153 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (141 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (48 : ℝ) * x^2 * (z - y)^4 + (18 : ℝ) * x^1 * (y - x)^5 + (45 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (156 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (189 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (108 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (24 : ℝ) * x^1 * (z - y)^5 + (7 : ℝ) * (y - x)^6 + (21 : ℝ) * (y - x)^5 * (z - y)^1 + (57 : ℝ) * (y - x)^4 * (z - y)^2 + (79 : ℝ) * (y - x)^3 * (z - y)^3 + (60 : ℝ) * (y - x)^2 * (z - y)^4 + (24 : ℝ) * (y - x)^1 * (z - y)^5 + (4 : ℝ) * (z - y)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - x) := by linarith
          have hdiff2 : 0 ≤ (y - z) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * x^4 * (z - x)^2 + (9 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (9 : ℝ) * x^4 * (y - z)^2 + (6 : ℝ) * x^3 * (z - x)^3 + (9 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (63 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (30 : ℝ) * x^3 * (y - z)^3 + (12 : ℝ) * x^2 * (z - x)^4 + (24 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (153 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (141 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (48 : ℝ) * x^2 * (y - z)^4 + (18 : ℝ) * x^1 * (z - x)^5 + (45 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (156 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (189 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (108 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (24 : ℝ) * x^1 * (y - z)^5 + (7 : ℝ) * (z - x)^6 + (21 : ℝ) * (z - x)^5 * (y - z)^1 + (57 : ℝ) * (z - x)^4 * (y - z)^2 + (79 : ℝ) * (z - x)^3 * (y - z)^3 + (60 : ℝ) * (z - x)^2 * (y - z)^4 + (24 : ℝ) * (z - x)^1 * (y - z)^5 + (4 : ℝ) * (y - z)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (x - z) := by linarith
          have hdiff2 : 0 ≤ (y - x) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * z^4 * (x - z)^2 + (9 : ℝ) * z^4 * (x - z)^1 * (y - x)^1 + (9 : ℝ) * z^4 * (y - x)^2 + (6 : ℝ) * z^3 * (x - z)^3 + (9 : ℝ) * z^3 * (x - z)^2 * (y - x)^1 + (63 : ℝ) * z^3 * (x - z)^1 * (y - x)^2 + (30 : ℝ) * z^3 * (y - x)^3 + (12 : ℝ) * z^2 * (x - z)^4 + (24 : ℝ) * z^2 * (x - z)^3 * (y - x)^1 + (153 : ℝ) * z^2 * (x - z)^2 * (y - x)^2 + (141 : ℝ) * z^2 * (x - z)^1 * (y - x)^3 + (48 : ℝ) * z^2 * (y - x)^4 + (18 : ℝ) * z^1 * (x - z)^5 + (45 : ℝ) * z^1 * (x - z)^4 * (y - x)^1 + (156 : ℝ) * z^1 * (x - z)^3 * (y - x)^2 + (189 : ℝ) * z^1 * (x - z)^2 * (y - x)^3 + (108 : ℝ) * z^1 * (x - z)^1 * (y - x)^4 + (24 : ℝ) * z^1 * (y - x)^5 + (7 : ℝ) * (x - z)^6 + (21 : ℝ) * (x - z)^5 * (y - x)^1 + (57 : ℝ) * (x - z)^4 * (y - x)^2 + (79 : ℝ) * (x - z)^3 * (y - x)^3 + (60 : ℝ) * (x - z)^2 * (y - x)^4 + (24 : ℝ) * (x - z)^1 * (y - x)^5 + (4 : ℝ) * (y - x)^6 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (x - y) := by linarith
        have hdiff2 : 0 ≤ (z - x) := by linarith
        have hpos : 0 ≤ (9 : ℝ) * y^4 * (x - y)^2 + (9 : ℝ) * y^4 * (x - y)^1 * (z - x)^1 + (9 : ℝ) * y^4 * (z - x)^2 + (6 : ℝ) * y^3 * (x - y)^3 + (9 : ℝ) * y^3 * (x - y)^2 * (z - x)^1 + (63 : ℝ) * y^3 * (x - y)^1 * (z - x)^2 + (30 : ℝ) * y^3 * (z - x)^3 + (12 : ℝ) * y^2 * (x - y)^4 + (24 : ℝ) * y^2 * (x - y)^3 * (z - x)^1 + (153 : ℝ) * y^2 * (x - y)^2 * (z - x)^2 + (141 : ℝ) * y^2 * (x - y)^1 * (z - x)^3 + (48 : ℝ) * y^2 * (z - x)^4 + (18 : ℝ) * y^1 * (x - y)^5 + (45 : ℝ) * y^1 * (x - y)^4 * (z - x)^1 + (156 : ℝ) * y^1 * (x - y)^3 * (z - x)^2 + (189 : ℝ) * y^1 * (x - y)^2 * (z - x)^3 + (108 : ℝ) * y^1 * (x - y)^1 * (z - x)^4 + (24 : ℝ) * y^1 * (z - x)^5 + (7 : ℝ) * (x - y)^6 + (21 : ℝ) * (x - y)^5 * (z - x)^1 + (57 : ℝ) * (x - y)^4 * (z - x)^2 + (79 : ℝ) * (x - y)^3 * (z - x)^3 + (60 : ℝ) * (x - y)^2 * (z - x)^4 + (24 : ℝ) * (x - y)^1 * (z - x)^5 + (4 : ℝ) * (z - x)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          have hdiff1 : 0 ≤ (z - y) := by linarith
          have hdiff2 : 0 ≤ (x - z) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * y^4 * (z - y)^2 + (9 : ℝ) * y^4 * (z - y)^1 * (x - z)^1 + (9 : ℝ) * y^4 * (x - z)^2 + (6 : ℝ) * y^3 * (z - y)^3 + (9 : ℝ) * y^3 * (z - y)^2 * (x - z)^1 + (63 : ℝ) * y^3 * (z - y)^1 * (x - z)^2 + (30 : ℝ) * y^3 * (x - z)^3 + (12 : ℝ) * y^2 * (z - y)^4 + (24 : ℝ) * y^2 * (z - y)^3 * (x - z)^1 + (153 : ℝ) * y^2 * (z - y)^2 * (x - z)^2 + (141 : ℝ) * y^2 * (z - y)^1 * (x - z)^3 + (48 : ℝ) * y^2 * (x - z)^4 + (18 : ℝ) * y^1 * (z - y)^5 + (45 : ℝ) * y^1 * (z - y)^4 * (x - z)^1 + (156 : ℝ) * y^1 * (z - y)^3 * (x - z)^2 + (189 : ℝ) * y^1 * (z - y)^2 * (x - z)^3 + (108 : ℝ) * y^1 * (z - y)^1 * (x - z)^4 + (24 : ℝ) * y^1 * (x - z)^5 + (7 : ℝ) * (z - y)^6 + (21 : ℝ) * (z - y)^5 * (x - z)^1 + (57 : ℝ) * (z - y)^4 * (x - z)^2 + (79 : ℝ) * (z - y)^3 * (x - z)^3 + (60 : ℝ) * (z - y)^2 * (x - z)^4 + (24 : ℝ) * (z - y)^1 * (x - z)^5 + (4 : ℝ) * (x - z)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (y - z) := by linarith
          have hdiff2 : 0 ≤ (x - y) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * z^4 * (y - z)^2 + (9 : ℝ) * z^4 * (y - z)^1 * (x - y)^1 + (9 : ℝ) * z^4 * (x - y)^2 + (6 : ℝ) * z^3 * (y - z)^3 + (9 : ℝ) * z^3 * (y - z)^2 * (x - y)^1 + (63 : ℝ) * z^3 * (y - z)^1 * (x - y)^2 + (30 : ℝ) * z^3 * (x - y)^3 + (12 : ℝ) * z^2 * (y - z)^4 + (24 : ℝ) * z^2 * (y - z)^3 * (x - y)^1 + (153 : ℝ) * z^2 * (y - z)^2 * (x - y)^2 + (141 : ℝ) * z^2 * (y - z)^1 * (x - y)^3 + (48 : ℝ) * z^2 * (x - y)^4 + (18 : ℝ) * z^1 * (y - z)^5 + (45 : ℝ) * z^1 * (y - z)^4 * (x - y)^1 + (156 : ℝ) * z^1 * (y - z)^3 * (x - y)^2 + (189 : ℝ) * z^1 * (y - z)^2 * (x - y)^3 + (108 : ℝ) * z^1 * (y - z)^1 * (x - y)^4 + (24 : ℝ) * z^1 * (x - y)^5 + (7 : ℝ) * (y - z)^6 + (21 : ℝ) * (y - z)^5 * (x - y)^1 + (57 : ℝ) * (y - z)^4 * (x - y)^2 + (79 : ℝ) * (y - z)^3 * (x - y)^3 + (60 : ℝ) * (y - z)^2 * (x - y)^4 + (24 : ℝ) * (y - z)^1 * (x - y)^5 + (4 : ℝ) * (x - y)^6 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 4 * (x ^ 6 + y ^ 6 + z ^ 6) + 27 * x ^ 2 * y ^ 2 * z ^ 2 ≥ 12 * (x ^ 4 * y * z + y ^ 4 * z * x + z ^ 4 * x * y) + (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3)) := @solution
#print axioms solution
