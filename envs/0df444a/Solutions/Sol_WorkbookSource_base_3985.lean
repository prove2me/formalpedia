-- Prove2me | solution 1 for WorkbookSource.base_3985
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:26.268327+00:00
-- url     : https://prove2.me/submissions/a9b47e06-bd50-46ca-b9f6-41d231a09ebc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2) : 24 * (a ^ 2 + b ^ 2 + c ^ 2) + (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ 48 + 8 * (a ^ 3 + b ^ 3 + c ^ 3)  := by
  have hp : 0 ≤ (4*a^3*b + 4*a^3*c + 4*a^2*b^2 + 24*a^2*b*c + 4*a^2*c^2 + 4*a*b^3 + 24*a*b^2*c + 24*a*b*c^2 + 4*a*c^3 + 4*b^3*c + 4*b^2*c^2 + 4*b*c^3) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (108 : ℝ) * a^4 + (288 : ℝ) * a^3 * (b - a)^1 + (144 : ℝ) * a^3 * (c - b)^1 + (272 : ℝ) * a^2 * (b - a)^2 + (272 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (56 : ℝ) * a^2 * (c - b)^2 + (104 : ℝ) * a^1 * (b - a)^3 + (156 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (68 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (8 : ℝ) * a^1 * (c - b)^3 + (12 : ℝ) * (b - a)^4 + (24 : ℝ) * (b - a)^3 * (c - b)^1 + (16 : ℝ) * (b - a)^2 * (c - b)^2 + (4 : ℝ) * (b - a)^1 * (c - b)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (108 : ℝ) * a^4 + (288 : ℝ) * a^3 * (c - a)^1 + (144 : ℝ) * a^3 * (b - c)^1 + (272 : ℝ) * a^2 * (c - a)^2 + (272 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (56 : ℝ) * a^2 * (b - c)^2 + (104 : ℝ) * a^1 * (c - a)^3 + (156 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (68 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (8 : ℝ) * a^1 * (b - c)^3 + (12 : ℝ) * (c - a)^4 + (24 : ℝ) * (c - a)^3 * (b - c)^1 + (16 : ℝ) * (c - a)^2 * (b - c)^2 + (4 : ℝ) * (c - a)^1 * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (108 : ℝ) * c^4 + (288 : ℝ) * c^3 * (a - c)^1 + (144 : ℝ) * c^3 * (b - a)^1 + (272 : ℝ) * c^2 * (a - c)^2 + (272 : ℝ) * c^2 * (a - c)^1 * (b - a)^1 + (56 : ℝ) * c^2 * (b - a)^2 + (104 : ℝ) * c^1 * (a - c)^3 + (156 : ℝ) * c^1 * (a - c)^2 * (b - a)^1 + (68 : ℝ) * c^1 * (a - c)^1 * (b - a)^2 + (8 : ℝ) * c^1 * (b - a)^3 + (12 : ℝ) * (a - c)^4 + (24 : ℝ) * (a - c)^3 * (b - a)^1 + (16 : ℝ) * (a - c)^2 * (b - a)^2 + (4 : ℝ) * (a - c)^1 * (b - a)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (108 : ℝ) * b^4 + (288 : ℝ) * b^3 * (a - b)^1 + (144 : ℝ) * b^3 * (c - a)^1 + (272 : ℝ) * b^2 * (a - b)^2 + (272 : ℝ) * b^2 * (a - b)^1 * (c - a)^1 + (56 : ℝ) * b^2 * (c - a)^2 + (104 : ℝ) * b^1 * (a - b)^3 + (156 : ℝ) * b^1 * (a - b)^2 * (c - a)^1 + (68 : ℝ) * b^1 * (a - b)^1 * (c - a)^2 + (8 : ℝ) * b^1 * (c - a)^3 + (12 : ℝ) * (a - b)^4 + (24 : ℝ) * (a - b)^3 * (c - a)^1 + (16 : ℝ) * (a - b)^2 * (c - a)^2 + (4 : ℝ) * (a - b)^1 * (c - a)^3 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (108 : ℝ) * b^4 + (288 : ℝ) * b^3 * (c - b)^1 + (144 : ℝ) * b^3 * (a - c)^1 + (272 : ℝ) * b^2 * (c - b)^2 + (272 : ℝ) * b^2 * (c - b)^1 * (a - c)^1 + (56 : ℝ) * b^2 * (a - c)^2 + (104 : ℝ) * b^1 * (c - b)^3 + (156 : ℝ) * b^1 * (c - b)^2 * (a - c)^1 + (68 : ℝ) * b^1 * (c - b)^1 * (a - c)^2 + (8 : ℝ) * b^1 * (a - c)^3 + (12 : ℝ) * (c - b)^4 + (24 : ℝ) * (c - b)^3 * (a - c)^1 + (16 : ℝ) * (c - b)^2 * (a - c)^2 + (4 : ℝ) * (c - b)^1 * (a - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (108 : ℝ) * c^4 + (288 : ℝ) * c^3 * (b - c)^1 + (144 : ℝ) * c^3 * (a - b)^1 + (272 : ℝ) * c^2 * (b - c)^2 + (272 : ℝ) * c^2 * (b - c)^1 * (a - b)^1 + (56 : ℝ) * c^2 * (a - b)^2 + (104 : ℝ) * c^1 * (b - c)^3 + (156 : ℝ) * c^1 * (b - c)^2 * (a - b)^1 + (68 : ℝ) * c^1 * (b - c)^1 * (a - b)^2 + (8 : ℝ) * c^1 * (a - b)^3 + (12 : ℝ) * (b - c)^4 + (24 : ℝ) * (b - c)^3 * (a - b)^1 + (16 : ℝ) * (b - c)^2 * (a - b)^2 + (4 : ℝ) * (b - c)^1 * (a - b)^3 := by positivity
          convert hpos using 1 <;> ring
  have he : (-a^4 + 8*a^3 - 2*a^2*b^2 - 2*a^2*c^2 - 24*a^2 - b^4 + 8*b^3 - 2*b^2*c^2 - 24*b^2 - c^4 + 8*c^3 - 24*c^2 + 48) = (4*a^3*b + 4*a^3*c + 4*a^2*b^2 + 24*a^2*b*c + 4*a^2*c^2 + 4*a*b^3 + 24*a*b^2*c + 24*a*b*c^2 + 4*a*c^3 + 4*b^3*c + 4*b^2*c^2 + 4*b*c^3) := by
    linear_combination (-a^3 - 3*a^2*b - 3*a^2*c + 6*a^2 - 3*a*b^2 - 18*a*b*c - 12*a*b - 3*a*c^2 - 12*a*c - 12*a - b^3 - 3*b^2*c + 6*b^2 - 3*b*c^2 - 12*b*c - 12*b - c^3 + 6*c^2 - 12*c - 24) * habc
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2), 24 * (a ^ 2 + b ^ 2 + c ^ 2) + (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ 48 + 8 * (a ^ 3 + b ^ 3 + c ^ 3)) := @solution
#print axioms solution
