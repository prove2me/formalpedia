-- Prove2me | solution 1 for WorkbookSource.plus_23444
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:42:08.626888+00:00
-- url     : https://prove2.me/submissions/0fbcd9e0-06cb-4df0-8150-49e29903d485

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 2 / (a * b + b * c + c * a) + 1 / (a^2 * b + b^2 * c + c^2 * a) ≥ 1   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (7*a^4*b/27 + a^4*c/27 - 4*a^3*b^2/9 - 8*a^3*b*c/27 + a^3*c^2/3 + a^2*b^3/3 + a^2*b^2*c/9 + a^2*b*c^2/9 - 4*a^2*c^3/9 + a*b^4/27 - 8*a*b^3*c/27 + a*b^2*c^2/9 - 8*a*b*c^3/27 + 7*a*c^4/27 + 7*b^4*c/27 - 4*b^3*c^2/9 + b^2*c^3/3 + b*c^4/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * a^3 * (b - a)^2 + (2/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (2/3 : ℝ) * a^3 * (c - b)^2 + (11/9 : ℝ) * a^2 * (b - a)^3 + (7/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (8/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (7/9 : ℝ) * a^2 * (c - b)^3 + (20/27 : ℝ) * a^1 * (b - a)^4 + (58/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (28/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (46/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (8/27 : ℝ) * a^1 * (c - b)^4 + (5/27 : ℝ) * (b - a)^5 + (14/27 : ℝ) * (b - a)^4 * (c - b)^1 + (7/9 : ℝ) * (b - a)^3 * (c - b)^2 + (13/27 : ℝ) * (b - a)^2 * (c - b)^3 + (1/27 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (7*a^4*b/27 + a^4*c/27 - 4*a^3*b^2/9 - 8*a^3*b*c/27 + a^3*c^2/3 + a^2*b^3/3 + a^2*b^2*c/9 + a^2*b*c^2/9 - 4*a^2*c^3/9 + a*b^4/27 - 8*a*b^3*c/27 + a*b^2*c^2/9 - 8*a*b*c^3/27 + 7*a*c^4/27 + 7*b^4*c/27 - 4*b^3*c^2/9 + b^2*c^3/3 + b*c^4/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * a^3 * (c - a)^2 + (2/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (2/3 : ℝ) * a^3 * (b - c)^2 + (11/9 : ℝ) * a^2 * (c - a)^3 + (4/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (5/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (7/9 : ℝ) * a^2 * (b - c)^3 + (20/27 : ℝ) * a^1 * (c - a)^4 + (22/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (10/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (28/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (8/27 : ℝ) * a^1 * (b - c)^4 + (5/27 : ℝ) * (c - a)^5 + (11/27 : ℝ) * (c - a)^4 * (b - c)^1 + (5/9 : ℝ) * (c - a)^3 * (b - c)^2 + (16/27 : ℝ) * (c - a)^2 * (b - c)^3 + (7/27 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (7*a^4*b/27 + a^4*c/27 - 4*a^3*b^2/9 - 8*a^3*b*c/27 + a^3*c^2/3 + a^2*b^3/3 + a^2*b^2*c/9 + a^2*b*c^2/9 - 4*a^2*c^3/9 + a*b^4/27 - 8*a*b^3*c/27 + a*b^2*c^2/9 - 8*a*b*c^3/27 + 7*a*c^4/27 + 7*b^4*c/27 - 4*b^3*c^2/9 + b^2*c^3/3 + b*c^4/27) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-a^3*b^2 - a^3*b*c - a^2*b^2*c - a^2*b*c^2 + 2*a^2*b - a^2*c^3 - a*b^3*c - a*b^2*c^2 - a*b*c^3 + a*b + 2*a*c^2 + a*c - b^3*c^2 + 2*b^2*c + b*c) = (7*a^4*b/27 + a^4*c/27 - 4*a^3*b^2/9 - 8*a^3*b*c/27 + a^3*c^2/3 + a^2*b^3/3 + a^2*b^2*c/9 + a^2*b*c^2/9 - 4*a^2*c^3/9 + a*b^4/27 - 8*a*b^3*c/27 + a*b^2*c^2/9 - 8*a*b*c^3/27 + 7*a*c^4/27 + 7*b^4*c/27 - 4*b^3*c^2/9 + b^2*c^3/3 + b*c^4/27) := by
    linear_combination (-7*a^3*b/27 - a^3*c/27 - 8*a^2*b^2/27 - 11*a^2*b*c/27 - 7*a^2*b/9 - 8*a^2*c^2/27 - a^2*c/9 - a*b^3/27 - 11*a*b^2*c/27 - a*b^2/9 - 11*a*b*c^2/27 - a*b*c/3 - a*b/3 - 7*a*c^3/27 - 7*a*c^2/9 - a*c/3 - 7*b^3*c/27 - 8*b^2*c^2/27 - 7*b^2*c/9 - b*c^3/27 - b*c^2/9 - b*c/3) * hab
  have hn : 0 ≤ (-a^3*b^2 - a^3*b*c - a^2*b^2*c - a^2*b*c^2 + 2*a^2*b - a^2*c^3 - a*b^3*c - a*b^2*c^2 - a*b*c^3 + a*b + 2*a*c^2 + a*c - b^3*c^2 + 2*b^2*c + b*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), 2 / (a * b + b * c + c * a) + 1 / (a^2 * b + b^2 * c + c^2 * a) ≥ 1) := @solution
#print axioms solution
