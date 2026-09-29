-- Prove2me | solution 1 for WorkbookSource.base_3991
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:26.925889+00:00
-- url     : https://prove2.me/submissions/2cfdb8a0-5e82-4fc7-964a-837da41b2d3d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 2 * a ^ 6 + 2 * b ^ 6 + 2 * c ^ 6 + 16 * a ^ 3 * b ^ 3 + 16 * b ^ 3 * c ^ 3 + 16 * c ^ 3 * a ^ 3 ≥ 9 * a ^ 4 * (b ^ 2 + c ^ 2) + 9 * b ^ 4 * (c ^ 2 + a ^ 2) + 9 * c ^ 4 * (a ^ 2 + b ^ 2)  := by
  have hp : 0 ≤ (2*a^6 - 9*a^4*b^2 - 9*a^4*c^2 + 16*a^3*b^3 + 16*a^3*c^3 - 9*a^2*b^4 - 9*a^2*c^4 + 2*b^6 - 9*b^4*c^2 + 16*b^3*c^3 - 9*b^2*c^4 + 2*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (12 : ℝ) * a^2 * (b - a)^4 + (24 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (36 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (24 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (12 : ℝ) * a^2 * (c - b)^4 + (12 : ℝ) * a^1 * (b - a)^5 + (30 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (60 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (60 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (42 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * a^1 * (c - b)^5 + (2 : ℝ) * (b - a)^6 + (6 : ℝ) * (b - a)^5 * (c - b)^1 + (15 : ℝ) * (b - a)^4 * (c - b)^2 + (20 : ℝ) * (b - a)^3 * (c - b)^3 + (21 : ℝ) * (b - a)^2 * (c - b)^4 + (12 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * a^2 * (c - a)^4 + (24 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (36 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (24 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (12 : ℝ) * a^2 * (b - c)^4 + (12 : ℝ) * a^1 * (c - a)^5 + (30 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (60 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (60 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (42 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (12 : ℝ) * a^1 * (b - c)^5 + (2 : ℝ) * (c - a)^6 + (6 : ℝ) * (c - a)^5 * (b - c)^1 + (15 : ℝ) * (c - a)^4 * (b - c)^2 + (20 : ℝ) * (c - a)^3 * (b - c)^3 + (21 : ℝ) * (c - a)^2 * (b - c)^4 + (12 : ℝ) * (c - a)^1 * (b - c)^5 + (2 : ℝ) * (b - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * c^2 * (a - c)^4 + (24 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (36 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (24 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (12 : ℝ) * c^2 * (b - a)^4 + (12 : ℝ) * c^1 * (a - c)^5 + (30 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (60 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (60 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (42 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (12 : ℝ) * c^1 * (b - a)^5 + (2 : ℝ) * (a - c)^6 + (6 : ℝ) * (a - c)^5 * (b - a)^1 + (15 : ℝ) * (a - c)^4 * (b - a)^2 + (20 : ℝ) * (a - c)^3 * (b - a)^3 + (21 : ℝ) * (a - c)^2 * (b - a)^4 + (12 : ℝ) * (a - c)^1 * (b - a)^5 + (2 : ℝ) * (b - a)^6 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (12 : ℝ) * b^2 * (a - b)^4 + (24 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (36 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (24 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (12 : ℝ) * b^2 * (c - a)^4 + (12 : ℝ) * b^1 * (a - b)^5 + (30 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (60 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (60 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (42 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (12 : ℝ) * b^1 * (c - a)^5 + (2 : ℝ) * (a - b)^6 + (6 : ℝ) * (a - b)^5 * (c - a)^1 + (15 : ℝ) * (a - b)^4 * (c - a)^2 + (20 : ℝ) * (a - b)^3 * (c - a)^3 + (21 : ℝ) * (a - b)^2 * (c - a)^4 + (12 : ℝ) * (a - b)^1 * (c - a)^5 + (2 : ℝ) * (c - a)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * b^2 * (c - b)^4 + (24 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (36 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (24 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (12 : ℝ) * b^2 * (a - c)^4 + (12 : ℝ) * b^1 * (c - b)^5 + (30 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (60 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (60 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (42 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (12 : ℝ) * b^1 * (a - c)^5 + (2 : ℝ) * (c - b)^6 + (6 : ℝ) * (c - b)^5 * (a - c)^1 + (15 : ℝ) * (c - b)^4 * (a - c)^2 + (20 : ℝ) * (c - b)^3 * (a - c)^3 + (21 : ℝ) * (c - b)^2 * (a - c)^4 + (12 : ℝ) * (c - b)^1 * (a - c)^5 + (2 : ℝ) * (a - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (12 : ℝ) * c^2 * (b - c)^4 + (24 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (36 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (24 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (12 : ℝ) * c^2 * (a - b)^4 + (12 : ℝ) * c^1 * (b - c)^5 + (30 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (60 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (60 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (42 : ℝ) * c^1 * (b - c)^1 * (a - b)^4 + (12 : ℝ) * c^1 * (a - b)^5 + (2 : ℝ) * (b - c)^6 + (6 : ℝ) * (b - c)^5 * (a - b)^1 + (15 : ℝ) * (b - c)^4 * (a - b)^2 + (20 : ℝ) * (b - c)^3 * (a - b)^3 + (21 : ℝ) * (b - c)^2 * (a - b)^4 + (12 : ℝ) * (b - c)^1 * (a - b)^5 + (2 : ℝ) * (a - b)^6 := by positivity
          convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), 2 * a ^ 6 + 2 * b ^ 6 + 2 * c ^ 6 + 16 * a ^ 3 * b ^ 3 + 16 * b ^ 3 * c ^ 3 + 16 * c ^ 3 * a ^ 3 ≥ 9 * a ^ 4 * (b ^ 2 + c ^ 2) + 9 * b ^ 4 * (c ^ 2 + a ^ 2) + 9 * c ^ 4 * (a ^ 2 + b ^ 2)) := @solution
#print axioms solution
