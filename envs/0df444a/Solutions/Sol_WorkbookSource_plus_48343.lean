-- Prove2me | solution 1 for WorkbookSource.plus_48343
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:25:07.943931+00:00
-- url     : https://prove2.me/submissions/3e4dc962-65ba-4d1d-ba88-8acd4d9e6dfc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / b + b / c + c / a + 2 * a * b * c ≥ 5   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*c/27 + a^4*b^2/27 - 2*a^4*b*c/27 + a^4*c^2/9 + a^3*b^3/9 - a^3*b^2*c/3 - 8*a^3*b*c^2/27 + a^3*c^3/9 + a^2*b^4/9 - 8*a^2*b^3*c/27 + 11*a^2*b^2*c^2/9 - a^2*b*c^3/3 + a^2*c^4/27 + a*b^5/27 - 2*a*b^4*c/27 - a*b^3*c^2/3 - 8*a*b^2*c^3/27 - 2*a*b*c^4/27 + b^4*c^2/27 + b^3*c^3/9 + b^2*c^4/9 + b*c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1/3 : ℝ) * a^4 * (b - a)^2 + (1/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1/3 : ℝ) * a^4 * (c - b)^2 + (29/27 : ℝ) * a^3 * (b - a)^3 + (19/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (14/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (7/27 : ℝ) * a^3 * (c - b)^3 + (40/27 : ℝ) * a^2 * (b - a)^4 + (107/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (35/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (38/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (7/27 : ℝ) * a^2 * (c - b)^4 + (28/27 : ℝ) * a^1 * (b - a)^5 + (88/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (107/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (59/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (14/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1/27 : ℝ) * a^1 * (c - b)^5 + (8/27 : ℝ) * (b - a)^6 + (28/27 : ℝ) * (b - a)^5 * (c - b)^1 + (38/27 : ℝ) * (b - a)^4 * (c - b)^2 + (25/27 : ℝ) * (b - a)^3 * (c - b)^3 + (8/27 : ℝ) * (b - a)^2 * (c - b)^4 + (1/27 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*c/27 + a^4*b^2/27 - 2*a^4*b*c/27 + a^4*c^2/9 + a^3*b^3/9 - a^3*b^2*c/3 - 8*a^3*b*c^2/27 + a^3*c^3/9 + a^2*b^4/9 - 8*a^2*b^3*c/27 + 11*a^2*b^2*c^2/9 - a^2*b*c^3/3 + a^2*c^4/27 + a*b^5/27 - 2*a*b^4*c/27 - a*b^3*c^2/3 - 8*a*b^2*c^3/27 - 2*a*b*c^4/27 + b^4*c^2/27 + b^3*c^3/9 + b^2*c^4/9 + b*c^5/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1/3 : ℝ) * a^4 * (c - a)^2 + (1/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (1/3 : ℝ) * a^4 * (b - c)^2 + (29/27 : ℝ) * a^3 * (c - a)^3 + (10/9 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (5/9 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (7/27 : ℝ) * a^3 * (b - c)^3 + (40/27 : ℝ) * a^2 * (c - a)^4 + (53/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (8/9 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (11/27 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (7/27 : ℝ) * a^2 * (b - c)^4 + (28/27 : ℝ) * a^1 * (c - a)^5 + (52/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (35/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (14/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (5/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1/27 : ℝ) * a^1 * (b - c)^5 + (8/27 : ℝ) * (c - a)^6 + (20/27 : ℝ) * (c - a)^5 * (b - c)^1 + (2/3 : ℝ) * (c - a)^4 * (b - c)^2 + (7/27 : ℝ) * (c - a)^3 * (b - c)^3 + (1/27 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*c/27 + a^4*b^2/27 - 2*a^4*b*c/27 + a^4*c^2/9 + a^3*b^3/9 - a^3*b^2*c/3 - 8*a^3*b*c^2/27 + a^3*c^3/9 + a^2*b^4/9 - 8*a^2*b^3*c/27 + 11*a^2*b^2*c^2/9 - a^2*b*c^3/3 + a^2*c^4/27 + a*b^5/27 - 2*a*b^4*c/27 - a*b^3*c^2/3 - 8*a*b^2*c^3/27 - 2*a*b*c^4/27 + b^4*c^2/27 + b^3*c^3/9 + b^2*c^4/9 + b*c^5/27) := by
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
  have he : (2*a^2*b^2*c^2 + a^2*c + a*b^2 - 5*a*b*c + b*c^2) = (a^5*c/27 + a^4*b^2/27 - 2*a^4*b*c/27 + a^4*c^2/9 + a^3*b^3/9 - a^3*b^2*c/3 - 8*a^3*b*c^2/27 + a^3*c^3/9 + a^2*b^4/9 - 8*a^2*b^3*c/27 + 11*a^2*b^2*c^2/9 - a^2*b*c^3/3 + a^2*c^4/27 + a*b^5/27 - 2*a*b^4*c/27 - a*b^3*c^2/3 - 8*a*b^2*c^3/27 - 2*a*b*c^4/27 + b^4*c^2/27 + b^3*c^3/9 + b^2*c^4/9 + b*c^5/27) := by
    linear_combination (-a^4*c/27 - a^3*b^2/27 + a^3*b*c/9 - 2*a^3*c^2/27 - a^3*c/9 - 2*a^2*b^3/27 + 7*a^2*b^2*c/27 - a^2*b^2/9 + 7*a^2*b*c^2/27 + 4*a^2*b*c/9 - a^2*c^3/27 - a^2*c^2/9 - a^2*c/3 - a*b^4/27 + a*b^3*c/9 - a*b^3/9 + 7*a*b^2*c^2/27 + 4*a*b^2*c/9 - a*b^2/3 + a*b*c^3/9 + 4*a*b*c^2/9 + 5*a*b*c/3 - b^3*c^2/27 - 2*b^2*c^3/27 - b^2*c^2/9 - b*c^4/27 - b*c^3/9 - b*c^2/3) * habc
  have hn : 0 ≤ (2*a^2*b^2*c^2 + a^2*c + a*b^2 - 5*a*b*c + b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a / b + b / c + c / a + 2 * a * b * c ≥ 5) := @solution
#print axioms solution
