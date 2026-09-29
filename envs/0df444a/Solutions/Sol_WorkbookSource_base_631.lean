-- Prove2me | solution 1 for WorkbookSource.base_631
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:42.65896+00:00
-- url     : https://prove2.me/submissions/e4eaec61-77ec-47cb-bbbf-403489dbcba6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * b / (2 * b + 1) + b * c / (2 * c + 1) + c * a / (2 * a + 1)) ≤ 1  := by
  have hp : 0 ≤ (7*a^4/81 + a^3*b/81 + 55*a^3*c/81 + 14*a^2*b^2/27 - 35*a^2*b*c/27 + 14*a^2*c^2/27 + 55*a*b^3/81 - 35*a*b^2*c/27 - 35*a*b*c^2/27 + a*c^3/81 + 7*b^4/81 + b^3*c/81 + 14*b^2*c^2/27 + 55*b*c^3/81 + 7*c^4/81) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (7/3 : ℝ) * a^2 * (b - a)^2 + (7/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (7/3 : ℝ) * a^2 * (c - b)^2 + (98/27 : ℝ) * a^1 * (b - a)^3 + (58/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (44/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (28/27 : ℝ) * a^1 * (c - b)^3 + (112/81 : ℝ) * (b - a)^4 + (278/81 : ℝ) * (b - a)^3 * (c - b)^1 + (83/27 : ℝ) * (b - a)^2 * (c - b)^2 + (83/81 : ℝ) * (b - a)^1 * (c - b)^3 + (7/81 : ℝ) * (c - b)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (7/3 : ℝ) * a^2 * (c - a)^2 + (7/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (7/3 : ℝ) * a^2 * (b - c)^2 + (98/27 : ℝ) * a^1 * (c - a)^3 + (40/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (26/9 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (28/27 : ℝ) * a^1 * (b - c)^3 + (112/81 : ℝ) * (c - a)^4 + (170/81 : ℝ) * (c - a)^3 * (b - c)^1 + (29/27 : ℝ) * (c - a)^2 * (b - c)^2 + (29/81 : ℝ) * (c - a)^1 * (b - c)^3 + (7/81 : ℝ) * (b - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (7/3 : ℝ) * c^2 * (a - c)^2 + (7/3 : ℝ) * c^2 * (a - c)^1 * (b - a)^1 + (7/3 : ℝ) * c^2 * (b - a)^2 + (98/27 : ℝ) * c^1 * (a - c)^3 + (58/9 : ℝ) * c^1 * (a - c)^2 * (b - a)^1 + (44/9 : ℝ) * c^1 * (a - c)^1 * (b - a)^2 + (28/27 : ℝ) * c^1 * (b - a)^3 + (112/81 : ℝ) * (a - c)^4 + (278/81 : ℝ) * (a - c)^3 * (b - a)^1 + (83/27 : ℝ) * (a - c)^2 * (b - a)^2 + (83/81 : ℝ) * (a - c)^1 * (b - a)^3 + (7/81 : ℝ) * (b - a)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (7/3 : ℝ) * b^2 * (a - b)^2 + (7/3 : ℝ) * b^2 * (a - b)^1 * (c - a)^1 + (7/3 : ℝ) * b^2 * (c - a)^2 + (98/27 : ℝ) * b^1 * (a - b)^3 + (40/9 : ℝ) * b^1 * (a - b)^2 * (c - a)^1 + (26/9 : ℝ) * b^1 * (a - b)^1 * (c - a)^2 + (28/27 : ℝ) * b^1 * (c - a)^3 + (112/81 : ℝ) * (a - b)^4 + (170/81 : ℝ) * (a - b)^3 * (c - a)^1 + (29/27 : ℝ) * (a - b)^2 * (c - a)^2 + (29/81 : ℝ) * (a - b)^1 * (c - a)^3 + (7/81 : ℝ) * (c - a)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (7/3 : ℝ) * b^2 * (c - b)^2 + (7/3 : ℝ) * b^2 * (c - b)^1 * (a - c)^1 + (7/3 : ℝ) * b^2 * (a - c)^2 + (98/27 : ℝ) * b^1 * (c - b)^3 + (58/9 : ℝ) * b^1 * (c - b)^2 * (a - c)^1 + (44/9 : ℝ) * b^1 * (c - b)^1 * (a - c)^2 + (28/27 : ℝ) * b^1 * (a - c)^3 + (112/81 : ℝ) * (c - b)^4 + (278/81 : ℝ) * (c - b)^3 * (a - c)^1 + (83/27 : ℝ) * (c - b)^2 * (a - c)^2 + (83/81 : ℝ) * (c - b)^1 * (a - c)^3 + (7/81 : ℝ) * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (7/3 : ℝ) * c^2 * (b - c)^2 + (7/3 : ℝ) * c^2 * (b - c)^1 * (a - b)^1 + (7/3 : ℝ) * c^2 * (a - b)^2 + (98/27 : ℝ) * c^1 * (b - c)^3 + (40/9 : ℝ) * c^1 * (b - c)^2 * (a - b)^1 + (26/9 : ℝ) * c^1 * (b - c)^1 * (a - b)^2 + (28/27 : ℝ) * c^1 * (a - b)^3 + (112/81 : ℝ) * (b - c)^4 + (170/81 : ℝ) * (b - c)^3 * (a - b)^1 + (29/27 : ℝ) * (b - c)^2 * (a - b)^2 + (29/81 : ℝ) * (b - c)^1 * (a - b)^3 + (7/81 : ℝ) * (a - b)^4 := by positivity
          convert hpos using 1 <;> ring
  have he : (-4*a^2*b*c - 2*a^2*b - 4*a*b^2*c - 4*a*b*c^2 + 2*a*b*c + 3*a*b - 2*a*c^2 + 3*a*c + 2*a - 2*b^2*c + 3*b*c + 2*b + 2*c + 1) = (7*a^4/81 + a^3*b/81 + 55*a^3*c/81 + 14*a^2*b^2/27 - 35*a^2*b*c/27 + 14*a^2*c^2/27 + 55*a*b^3/81 - 35*a*b^2*c/27 - 35*a*b*c^2/27 + a*c^3/81 + 7*b^4/81 + b^3*c/81 + 14*b^2*c^2/27 + 55*b*c^3/81 + 7*c^4/81) := by
    linear_combination (-7*a^3/81 + 2*a^2*b/27 - 16*a^2*c/27 - 7*a^2/27 - 16*a*b^2/27 - 59*a*b*c/27 - 41*a*b/27 + 2*a*c^2/27 - 41*a*c/27 - 7*a/9 - 7*b^3/81 + 2*b^2*c/27 - 7*b^2/27 - 16*b*c^2/27 - 41*b*c/27 - 7*b/9 - 7*c^3/81 - 7*c^2/27 - 7*c/9 - 1/3) * hab
  have hn : 0 ≤ (-4*a^2*b*c - 2*a^2*b - 4*a*b^2*c - 4*a*b*c^2 + 2*a*b*c + 3*a*b - 2*a*c^2 + 3*a*c + 2*a - 2*b^2*c + 3*b*c + 2*b + 2*c + 1) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a * b / (2 * b + 1) + b * c / (2 * c + 1) + c * a / (2 * a + 1)) ≤ 1) := @solution
#print axioms solution
