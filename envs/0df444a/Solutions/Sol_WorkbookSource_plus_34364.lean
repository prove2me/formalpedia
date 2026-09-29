-- Prove2me | solution 1 for WorkbookSource.plus_34364
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:28.524722+00:00
-- url     : https://prove2.me/submissions/d20b3f1a-f5d8-4f61-8f8d-a40a73d149a5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (a * b * c) + 4 / (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + a * b * c) ≥ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b/27 + a^4*b^2/9 + 8*a^4*b*c/27 + a^4*c^2/27 + a^3*b^3/9 - 32*a^3*b^2*c/27 + 7*a^3*b*c^2/9 + a^3*c^3/9 + a^2*b^4/27 + 7*a^2*b^3*c/9 - 5*a^2*b^2*c^2/9 - 32*a^2*b*c^3/27 + a^2*c^4/9 + 8*a*b^4*c/27 - 32*a*b^3*c^2/27 + 7*a*b^2*c^3/9 + 8*a*b*c^4/27 + a*c^5/27 + b^5*c/27 + b^4*c^2/9 + b^3*c^3/9 + b^2*c^4/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5/3 : ℝ) * a^4 * (b - a)^2 + (5/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (5/3 : ℝ) * a^4 * (c - b)^2 + (127/27 : ℝ) * a^3 * (b - a)^3 + (68/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (61/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (53/27 : ℝ) * a^3 * (c - b)^3 + (128/27 : ℝ) * a^2 * (b - a)^4 + (283/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (94/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (127/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (17/27 : ℝ) * a^2 * (c - b)^4 + (2 : ℝ) * a^1 * (b - a)^5 + (16/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (161/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (28/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (5/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1/27 : ℝ) * a^1 * (c - b)^5 + (8/27 : ℝ) * (b - a)^6 + (20/27 : ℝ) * (b - a)^5 * (c - b)^1 + (2/3 : ℝ) * (b - a)^4 * (c - b)^2 + (7/27 : ℝ) * (b - a)^3 * (c - b)^3 + (1/27 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b/27 + a^4*b^2/9 + 8*a^4*b*c/27 + a^4*c^2/27 + a^3*b^3/9 - 32*a^3*b^2*c/27 + 7*a^3*b*c^2/9 + a^3*c^3/9 + a^2*b^4/27 + 7*a^2*b^3*c/9 - 5*a^2*b^2*c^2/9 - 32*a^2*b*c^3/27 + a^2*c^4/9 + 8*a*b^4*c/27 - 32*a*b^3*c^2/27 + 7*a*b^2*c^3/9 + 8*a*b*c^4/27 + a*c^5/27 + b^5*c/27 + b^4*c^2/9 + b^3*c^3/9 + b^2*c^4/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (5/3 : ℝ) * a^4 * (c - a)^2 + (5/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (5/3 : ℝ) * a^4 * (b - c)^2 + (127/27 : ℝ) * a^3 * (c - a)^3 + (59/9 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (52/9 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (53/27 : ℝ) * a^3 * (b - c)^3 + (128/27 : ℝ) * a^2 * (c - a)^4 + (229/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (67/9 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (100/27 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (17/27 : ℝ) * a^2 * (b - c)^4 + (2 : ℝ) * a^1 * (c - a)^5 + (14/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (125/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (25/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (8/9 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1/27 : ℝ) * a^1 * (b - c)^5 + (8/27 : ℝ) * (c - a)^6 + (28/27 : ℝ) * (c - a)^5 * (b - c)^1 + (38/27 : ℝ) * (c - a)^4 * (b - c)^2 + (25/27 : ℝ) * (c - a)^3 * (b - c)^3 + (8/27 : ℝ) * (c - a)^2 * (b - c)^4 + (1/27 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b/27 + a^4*b^2/9 + 8*a^4*b*c/27 + a^4*c^2/27 + a^3*b^3/9 - 32*a^3*b^2*c/27 + 7*a^3*b*c^2/9 + a^3*c^3/9 + a^2*b^4/27 + 7*a^2*b^3*c/9 - 5*a^2*b^2*c^2/9 - 32*a^2*b*c^3/27 + a^2*c^4/9 + 8*a*b^4*c/27 - 32*a*b^3*c^2/27 + 7*a*b^2*c^3/9 + 8*a*b*c^4/27 + a*c^5/27 + b^5*c/27 + b^4*c^2/9 + b^3*c^3/9 + b^2*c^4/27) := by
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
  have he : (-2*a^3*b^2*c - 2*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*b - 2*a*b^3*c^2 + 5*a*b*c + a*c^2 + b^2*c) = (a^5*b/27 + a^4*b^2/9 + 8*a^4*b*c/27 + a^4*c^2/27 + a^3*b^3/9 - 32*a^3*b^2*c/27 + 7*a^3*b*c^2/9 + a^3*c^3/9 + a^2*b^4/27 + 7*a^2*b^3*c/9 - 5*a^2*b^2*c^2/9 - 32*a^2*b*c^3/27 + a^2*c^4/9 + 8*a*b^4*c/27 - 32*a*b^3*c^2/27 + 7*a*b^2*c^3/9 + 8*a*b*c^4/27 + a*c^5/27 + b^5*c/27 + b^4*c^2/9 + b^3*c^3/9 + b^2*c^4/27) := by
    linear_combination (-a^4*b/27 - 2*a^3*b^2/27 - 7*a^3*b*c/27 - a^3*b/9 - a^3*c^2/27 - a^2*b^3/27 - 13*a^2*b^2*c/27 - a^2*b^2/9 - 13*a^2*b*c^2/27 - 2*a^2*b*c/3 - a^2*b/3 - 2*a^2*c^3/27 - a^2*c^2/9 - 7*a*b^3*c/27 - 13*a*b^2*c^2/27 - 2*a*b^2*c/3 - 7*a*b*c^3/27 - 2*a*b*c^2/3 - 5*a*b*c/3 - a*c^4/27 - a*c^3/9 - a*c^2/3 - b^4*c/27 - 2*b^3*c^2/27 - b^3*c/9 - b^2*c^3/27 - b^2*c^2/9 - b^2*c/3) * hab
  have hn : 0 ≤ (-2*a^3*b^2*c - 2*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*b - 2*a*b^3*c^2 + 5*a*b*c + a*c^2 + b^2*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), 1 / (a * b * c) + 4 / (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + a * b * c) ≥ 2) := @solution
#print axioms solution
