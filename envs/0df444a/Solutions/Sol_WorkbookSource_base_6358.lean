-- Prove2me | solution 1 for WorkbookSource.base_6358
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:32.266646+00:00
-- url     : https://prove2.me/submissions/22cb915a-52ea-4e9b-8214-86be376e5542

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 5 ≥ 81 * a * b * c * (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have hp : 0 ≤ (a^5 + 5*a^4*b + 5*a^4*c + 10*a^3*b^2 - 61*a^3*b*c + 10*a^3*c^2 + 10*a^2*b^3 + 30*a^2*b^2*c + 30*a^2*b*c^2 + 10*a^2*c^3 + 5*a*b^4 - 61*a*b^3*c + 30*a*b^2*c^2 - 61*a*b*c^3 + 5*a*c^4 + b^5 + 5*b^4*c + 10*b^3*c^2 + 10*b^2*c^3 + 5*b*c^4 + c^5) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (27 : ℝ) * a^3 * (b - a)^2 + (27 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (27 : ℝ) * a^3 * (c - b)^2 + (72 : ℝ) * a^2 * (b - a)^3 + (108 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (54 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (9 : ℝ) * a^2 * (c - b)^3 + (78 : ℝ) * a^1 * (b - a)^4 + (156 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (117 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (39 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (15 : ℝ) * a^1 * (c - b)^4 + (32 : ℝ) * (b - a)^5 + (80 : ℝ) * (b - a)^4 * (c - b)^1 + (80 : ℝ) * (b - a)^3 * (c - b)^2 + (40 : ℝ) * (b - a)^2 * (c - b)^3 + (10 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (27 : ℝ) * a^3 * (c - a)^2 + (27 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (27 : ℝ) * a^3 * (b - c)^2 + (72 : ℝ) * a^2 * (c - a)^3 + (108 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (54 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (9 : ℝ) * a^2 * (b - c)^3 + (78 : ℝ) * a^1 * (c - a)^4 + (156 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (117 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (39 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (15 : ℝ) * a^1 * (b - c)^4 + (32 : ℝ) * (c - a)^5 + (80 : ℝ) * (c - a)^4 * (b - c)^1 + (80 : ℝ) * (c - a)^3 * (b - c)^2 + (40 : ℝ) * (c - a)^2 * (b - c)^3 + (10 : ℝ) * (c - a)^1 * (b - c)^4 + (1 : ℝ) * (b - c)^5 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (27 : ℝ) * c^3 * (a - c)^2 + (27 : ℝ) * c^3 * (a - c)^1 * (b - a)^1 + (27 : ℝ) * c^3 * (b - a)^2 + (72 : ℝ) * c^2 * (a - c)^3 + (108 : ℝ) * c^2 * (a - c)^2 * (b - a)^1 + (54 : ℝ) * c^2 * (a - c)^1 * (b - a)^2 + (9 : ℝ) * c^2 * (b - a)^3 + (78 : ℝ) * c^1 * (a - c)^4 + (156 : ℝ) * c^1 * (a - c)^3 * (b - a)^1 + (117 : ℝ) * c^1 * (a - c)^2 * (b - a)^2 + (39 : ℝ) * c^1 * (a - c)^1 * (b - a)^3 + (15 : ℝ) * c^1 * (b - a)^4 + (32 : ℝ) * (a - c)^5 + (80 : ℝ) * (a - c)^4 * (b - a)^1 + (80 : ℝ) * (a - c)^3 * (b - a)^2 + (40 : ℝ) * (a - c)^2 * (b - a)^3 + (10 : ℝ) * (a - c)^1 * (b - a)^4 + (1 : ℝ) * (b - a)^5 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (27 : ℝ) * b^3 * (a - b)^2 + (27 : ℝ) * b^3 * (a - b)^1 * (c - a)^1 + (27 : ℝ) * b^3 * (c - a)^2 + (72 : ℝ) * b^2 * (a - b)^3 + (108 : ℝ) * b^2 * (a - b)^2 * (c - a)^1 + (54 : ℝ) * b^2 * (a - b)^1 * (c - a)^2 + (9 : ℝ) * b^2 * (c - a)^3 + (78 : ℝ) * b^1 * (a - b)^4 + (156 : ℝ) * b^1 * (a - b)^3 * (c - a)^1 + (117 : ℝ) * b^1 * (a - b)^2 * (c - a)^2 + (39 : ℝ) * b^1 * (a - b)^1 * (c - a)^3 + (15 : ℝ) * b^1 * (c - a)^4 + (32 : ℝ) * (a - b)^5 + (80 : ℝ) * (a - b)^4 * (c - a)^1 + (80 : ℝ) * (a - b)^3 * (c - a)^2 + (40 : ℝ) * (a - b)^2 * (c - a)^3 + (10 : ℝ) * (a - b)^1 * (c - a)^4 + (1 : ℝ) * (c - a)^5 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (27 : ℝ) * b^3 * (c - b)^2 + (27 : ℝ) * b^3 * (c - b)^1 * (a - c)^1 + (27 : ℝ) * b^3 * (a - c)^2 + (72 : ℝ) * b^2 * (c - b)^3 + (108 : ℝ) * b^2 * (c - b)^2 * (a - c)^1 + (54 : ℝ) * b^2 * (c - b)^1 * (a - c)^2 + (9 : ℝ) * b^2 * (a - c)^3 + (78 : ℝ) * b^1 * (c - b)^4 + (156 : ℝ) * b^1 * (c - b)^3 * (a - c)^1 + (117 : ℝ) * b^1 * (c - b)^2 * (a - c)^2 + (39 : ℝ) * b^1 * (c - b)^1 * (a - c)^3 + (15 : ℝ) * b^1 * (a - c)^4 + (32 : ℝ) * (c - b)^5 + (80 : ℝ) * (c - b)^4 * (a - c)^1 + (80 : ℝ) * (c - b)^3 * (a - c)^2 + (40 : ℝ) * (c - b)^2 * (a - c)^3 + (10 : ℝ) * (c - b)^1 * (a - c)^4 + (1 : ℝ) * (a - c)^5 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (27 : ℝ) * c^3 * (b - c)^2 + (27 : ℝ) * c^3 * (b - c)^1 * (a - b)^1 + (27 : ℝ) * c^3 * (a - b)^2 + (72 : ℝ) * c^2 * (b - c)^3 + (108 : ℝ) * c^2 * (b - c)^2 * (a - b)^1 + (54 : ℝ) * c^2 * (b - c)^1 * (a - b)^2 + (9 : ℝ) * c^2 * (a - b)^3 + (78 : ℝ) * c^1 * (b - c)^4 + (156 : ℝ) * c^1 * (b - c)^3 * (a - b)^1 + (117 : ℝ) * c^1 * (b - c)^2 * (a - b)^2 + (39 : ℝ) * c^1 * (b - c)^1 * (a - b)^3 + (15 : ℝ) * c^1 * (a - b)^4 + (32 : ℝ) * (b - c)^5 + (80 : ℝ) * (b - c)^4 * (a - b)^1 + (80 : ℝ) * (b - c)^3 * (a - b)^2 + (40 : ℝ) * (b - c)^2 * (a - b)^3 + (10 : ℝ) * (b - c)^1 * (a - b)^4 + (1 : ℝ) * (a - b)^5 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a + b + c) ^ 5 ≥ 81 * a * b * c * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
