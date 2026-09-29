-- Prove2me | solution 1 for WorkbookSource.base_5888
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:30.335652+00:00
-- url     : https://prove2.me/submissions/12be4b71-69ea-4911-842e-ce365969585d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 27 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2  := by
  have hp : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - 19*a^4*b*c + 10*a^3*b^3 - 2*a^3*b^2*c - 2*a^3*b*c^2 + 10*a^3*c^3 - 2*a^2*b^3*c + 24*a^2*b^2*c^2 - 2*a^2*b*c^3 + 2*a*b^5 - 19*a*b^4*c - 2*a*b^3*c^2 - 2*a*b^2*c^3 - 19*a*b*c^4 + 2*a*c^5 + b^6 + 2*b^5*c + 10*b^3*c^3 + 2*b*c^5 + c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (9 : ℝ) * a^4 * (b - a)^2 + (9 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^4 * (c - b)^2 + (36 : ℝ) * a^3 * (b - a)^3 + (54 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (18 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (70 : ℝ) * a^2 * (b - a)^4 + (140 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (102 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (32 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (16 : ℝ) * a^2 * (c - b)^4 + (58 : ℝ) * a^1 * (b - a)^5 + (145 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (158 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (92 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (41 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (10 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^6 + (48 : ℝ) * (b - a)^5 * (c - b)^1 + (65 : ℝ) * (b - a)^4 * (c - b)^2 + (50 : ℝ) * (b - a)^3 * (c - b)^3 + (25 : ℝ) * (b - a)^2 * (c - b)^4 + (8 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * a^4 * (c - a)^2 + (9 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (9 : ℝ) * a^4 * (b - c)^2 + (36 : ℝ) * a^3 * (c - a)^3 + (54 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (18 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (70 : ℝ) * a^2 * (c - a)^4 + (140 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (102 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (32 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (16 : ℝ) * a^2 * (b - c)^4 + (58 : ℝ) * a^1 * (c - a)^5 + (145 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (158 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (92 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (41 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (10 : ℝ) * a^1 * (b - c)^5 + (16 : ℝ) * (c - a)^6 + (48 : ℝ) * (c - a)^5 * (b - c)^1 + (65 : ℝ) * (c - a)^4 * (b - c)^2 + (50 : ℝ) * (c - a)^3 * (b - c)^3 + (25 : ℝ) * (c - a)^2 * (b - c)^4 + (8 : ℝ) * (c - a)^1 * (b - c)^5 + (1 : ℝ) * (b - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * c^4 * (a - c)^2 + (9 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (9 : ℝ) * c^4 * (b - a)^2 + (36 : ℝ) * c^3 * (a - c)^3 + (54 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (18 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (70 : ℝ) * c^2 * (a - c)^4 + (140 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (102 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (32 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (16 : ℝ) * c^2 * (b - a)^4 + (58 : ℝ) * c^1 * (a - c)^5 + (145 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (158 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (92 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (41 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (10 : ℝ) * c^1 * (b - a)^5 + (16 : ℝ) * (a - c)^6 + (48 : ℝ) * (a - c)^5 * (b - a)^1 + (65 : ℝ) * (a - c)^4 * (b - a)^2 + (50 : ℝ) * (a - c)^3 * (b - a)^3 + (25 : ℝ) * (a - c)^2 * (b - a)^4 + (8 : ℝ) * (a - c)^1 * (b - a)^5 + (1 : ℝ) * (b - a)^6 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (9 : ℝ) * b^4 * (a - b)^2 + (9 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (9 : ℝ) * b^4 * (c - a)^2 + (36 : ℝ) * b^3 * (a - b)^3 + (54 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (18 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (70 : ℝ) * b^2 * (a - b)^4 + (140 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (102 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (32 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (16 : ℝ) * b^2 * (c - a)^4 + (58 : ℝ) * b^1 * (a - b)^5 + (145 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (158 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (92 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (41 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (10 : ℝ) * b^1 * (c - a)^5 + (16 : ℝ) * (a - b)^6 + (48 : ℝ) * (a - b)^5 * (c - a)^1 + (65 : ℝ) * (a - b)^4 * (c - a)^2 + (50 : ℝ) * (a - b)^3 * (c - a)^3 + (25 : ℝ) * (a - b)^2 * (c - a)^4 + (8 : ℝ) * (a - b)^1 * (c - a)^5 + (1 : ℝ) * (c - a)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * b^4 * (c - b)^2 + (9 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (9 : ℝ) * b^4 * (a - c)^2 + (36 : ℝ) * b^3 * (c - b)^3 + (54 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (18 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (70 : ℝ) * b^2 * (c - b)^4 + (140 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (102 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (32 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (16 : ℝ) * b^2 * (a - c)^4 + (58 : ℝ) * b^1 * (c - b)^5 + (145 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (158 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (92 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (41 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (10 : ℝ) * b^1 * (a - c)^5 + (16 : ℝ) * (c - b)^6 + (48 : ℝ) * (c - b)^5 * (a - c)^1 + (65 : ℝ) * (c - b)^4 * (a - c)^2 + (50 : ℝ) * (c - b)^3 * (a - c)^3 + (25 : ℝ) * (c - b)^2 * (a - c)^4 + (8 : ℝ) * (c - b)^1 * (a - c)^5 + (1 : ℝ) * (a - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (9 : ℝ) * c^4 * (b - c)^2 + (9 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (9 : ℝ) * c^4 * (a - b)^2 + (36 : ℝ) * c^3 * (b - c)^3 + (54 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (18 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (70 : ℝ) * c^2 * (b - c)^4 + (140 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (102 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (32 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (16 : ℝ) * c^2 * (a - b)^4 + (58 : ℝ) * c^1 * (b - c)^5 + (145 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (158 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (92 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (41 : ℝ) * c^1 * (b - c)^1 * (a - b)^4 + (10 : ℝ) * c^1 * (a - b)^5 + (16 : ℝ) * (b - c)^6 + (48 : ℝ) * (b - c)^5 * (a - b)^1 + (65 : ℝ) * (b - c)^4 * (a - b)^2 + (50 : ℝ) * (b - c)^3 * (a - b)^3 + (25 : ℝ) * (b - c)^2 * (a - b)^4 + (8 : ℝ) * (b - c)^1 * (a - b)^5 + (1 : ℝ) * (a - b)^6 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a + b + c) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 27 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2) := @solution
#print axioms solution
