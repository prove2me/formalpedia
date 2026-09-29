-- Prove2me | solution 1 for WorkbookSource.base_2098
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:21.045226+00:00
-- url     : https://prove2.me/submissions/ac18003e-b876-48c8-9e45-fcdfba032f5d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : (3 * a - b * c) * (3 * b - c * a) * (3 * c - a * b) ≤ 8 * a * b * c  := by
  have hp : 0 ≤ (a^4*b^2 - 46*a^4*b*c/27 + a^4*c^2 + 2*a^3*b^3 - 10*a^3*b^2*c/9 - 10*a^3*b*c^2/9 + 2*a^3*c^3 + a^2*b^4 - 10*a^2*b^3*c/9 - 2*a^2*b^2*c^2/9 - 10*a^2*b*c^3/9 + a^2*c^4 - 46*a*b^4*c/27 - 10*a*b^3*c^2/9 - 10*a*b^2*c^3/9 - 46*a*b*c^4/27 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (20/3 : ℝ) * a^4 * (b - a)^2 + (20/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (20/3 : ℝ) * a^4 * (c - b)^2 + (640/27 : ℝ) * a^3 * (b - a)^3 + (320/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (160/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (80/27 : ℝ) * a^3 * (c - b)^3 + (848/27 : ℝ) * a^2 * (b - a)^4 + (1696/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (328/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (136/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (8/27 : ℝ) * a^2 * (c - b)^4 + (496/27 : ℝ) * a^1 * (b - a)^5 + (1240/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (112/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (272/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (8/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (13 : ℝ) * (b - a)^4 * (c - b)^2 + (6 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (20/3 : ℝ) * a^4 * (c - a)^2 + (20/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (20/3 : ℝ) * a^4 * (b - c)^2 + (640/27 : ℝ) * a^3 * (c - a)^3 + (320/9 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (160/9 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (80/27 : ℝ) * a^3 * (b - c)^3 + (848/27 : ℝ) * a^2 * (c - a)^4 + (1696/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (328/9 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (136/27 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (8/27 : ℝ) * a^2 * (b - c)^4 + (496/27 : ℝ) * a^1 * (c - a)^5 + (1240/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (112/3 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (272/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (8/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * (c - a)^6 + (12 : ℝ) * (c - a)^5 * (b - c)^1 + (13 : ℝ) * (c - a)^4 * (b - c)^2 + (6 : ℝ) * (c - a)^3 * (b - c)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (20/3 : ℝ) * c^4 * (a - c)^2 + (20/3 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (20/3 : ℝ) * c^4 * (b - a)^2 + (640/27 : ℝ) * c^3 * (a - c)^3 + (320/9 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (160/9 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (80/27 : ℝ) * c^3 * (b - a)^3 + (848/27 : ℝ) * c^2 * (a - c)^4 + (1696/27 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (328/9 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (136/27 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (8/27 : ℝ) * c^2 * (b - a)^4 + (496/27 : ℝ) * c^1 * (a - c)^5 + (1240/27 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (112/3 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (272/27 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (8/27 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (4 : ℝ) * (a - c)^6 + (12 : ℝ) * (a - c)^5 * (b - a)^1 + (13 : ℝ) * (a - c)^4 * (b - a)^2 + (6 : ℝ) * (a - c)^3 * (b - a)^3 + (1 : ℝ) * (a - c)^2 * (b - a)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (20/3 : ℝ) * b^4 * (a - b)^2 + (20/3 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (20/3 : ℝ) * b^4 * (c - a)^2 + (640/27 : ℝ) * b^3 * (a - b)^3 + (320/9 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (160/9 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (80/27 : ℝ) * b^3 * (c - a)^3 + (848/27 : ℝ) * b^2 * (a - b)^4 + (1696/27 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (328/9 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (136/27 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (8/27 : ℝ) * b^2 * (c - a)^4 + (496/27 : ℝ) * b^1 * (a - b)^5 + (1240/27 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (112/3 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (272/27 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (8/27 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (4 : ℝ) * (a - b)^6 + (12 : ℝ) * (a - b)^5 * (c - a)^1 + (13 : ℝ) * (a - b)^4 * (c - a)^2 + (6 : ℝ) * (a - b)^3 * (c - a)^3 + (1 : ℝ) * (a - b)^2 * (c - a)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (20/3 : ℝ) * b^4 * (c - b)^2 + (20/3 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (20/3 : ℝ) * b^4 * (a - c)^2 + (640/27 : ℝ) * b^3 * (c - b)^3 + (320/9 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (160/9 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (80/27 : ℝ) * b^3 * (a - c)^3 + (848/27 : ℝ) * b^2 * (c - b)^4 + (1696/27 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (328/9 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (136/27 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (8/27 : ℝ) * b^2 * (a - c)^4 + (496/27 : ℝ) * b^1 * (c - b)^5 + (1240/27 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (112/3 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (272/27 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (8/27 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (4 : ℝ) * (c - b)^6 + (12 : ℝ) * (c - b)^5 * (a - c)^1 + (13 : ℝ) * (c - b)^4 * (a - c)^2 + (6 : ℝ) * (c - b)^3 * (a - c)^3 + (1 : ℝ) * (c - b)^2 * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (20/3 : ℝ) * c^4 * (b - c)^2 + (20/3 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (20/3 : ℝ) * c^4 * (a - b)^2 + (640/27 : ℝ) * c^3 * (b - c)^3 + (320/9 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (160/9 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (80/27 : ℝ) * c^3 * (a - b)^3 + (848/27 : ℝ) * c^2 * (b - c)^4 + (1696/27 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (328/9 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (136/27 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (8/27 : ℝ) * c^2 * (a - b)^4 + (496/27 : ℝ) * c^1 * (b - c)^5 + (1240/27 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (112/3 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (272/27 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (8/27 : ℝ) * c^1 * (b - c)^1 * (a - b)^4 + (4 : ℝ) * (b - c)^6 + (12 : ℝ) * (b - c)^5 * (a - b)^1 + (13 : ℝ) * (b - c)^4 * (a - b)^2 + (6 : ℝ) * (b - c)^3 * (a - b)^3 + (1 : ℝ) * (b - c)^2 * (a - b)^4 := by positivity
          convert hpos using 1 <;> ring
  have he : (-3*a^3*b*c + a^2*b^2*c^2 + 9*a^2*b^2 + 9*a^2*c^2 - 3*a*b^3*c - 3*a*b*c^3 - 19*a*b*c + 9*b^2*c^2) = (a^4*b^2 - 46*a^4*b*c/27 + a^4*c^2 + 2*a^3*b^3 - 10*a^3*b^2*c/9 - 10*a^3*b*c^2/9 + 2*a^3*c^3 + a^2*b^4 - 10*a^2*b^3*c/9 - 2*a^2*b^2*c^2/9 - 10*a^2*b*c^3/9 + a^2*c^4 - 46*a*b^4*c/27 - 10*a*b^3*c^2/9 - 10*a*b^2*c^3/9 - 46*a*b*c^4/27 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    linear_combination (-a^3*b^2 + 46*a^3*b*c/27 - a^3*c^2 - a^2*b^3 + 11*a^2*b^2*c/27 - 3*a^2*b^2 + 11*a^2*b*c^2/27 + 19*a^2*b*c/9 - a^2*c^3 - 3*a^2*c^2 + 46*a*b^3*c/27 + 11*a*b^2*c^2/27 + 19*a*b^2*c/9 + 46*a*b*c^3/27 + 19*a*b*c^2/9 + 19*a*b*c/3 - b^3*c^2 - b^2*c^3 - 3*b^2*c^2) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), (3 * a - b * c) * (3 * b - c * a) * (3 * c - a * b) ≤ 8 * a * b * c) := @solution
#print axioms solution
