-- Prove2me | solution 1 for WorkbookSource.base_37298
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:07.52867+00:00
-- url     : https://prove2.me/submissions/17a6230c-562a-4d75-b5b6-ea54fb26f26e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (2 * a / (a + b) + 2 * b / (b + c) + 2 * c / (c + a)) ≤ a ^ 2 + b ^ 2 + c ^ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^4*b/9 + 7*a^4*c/9 - a^3*b^2/9 + a^3*c^2/9 + a^2*b^3/9 - 4*a^2*b^2*c/3 - 4*a^2*b*c^2/3 - a^2*c^3/9 + 7*a*b^4/9 - 4*a*b^2*c^2/3 + 5*a*c^4/9 + 5*b^4*c/9 - b^3*c^2/9 + b^2*c^3/9 + 7*b*c^4/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^3 * (b - a)^2 + (16/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (16/3 : ℝ) * a^3 * (c - b)^2 + (32/3 : ℝ) * a^2 * (b - a)^3 + (17 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (17 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (16/3 : ℝ) * a^2 * (c - b)^3 + (20/3 : ℝ) * a^1 * (b - a)^4 + (44/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (50/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (26/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (4/3 : ℝ) * a^1 * (c - b)^4 + (4/3 : ℝ) * (b - a)^5 + (34/9 : ℝ) * (b - a)^4 * (c - b)^1 + (44/9 : ℝ) * (b - a)^3 * (c - b)^2 + (29/9 : ℝ) * (b - a)^2 * (c - b)^3 + (7/9 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (5*a^4*b/9 + 7*a^4*c/9 - a^3*b^2/9 + a^3*c^2/9 + a^2*b^3/9 - 4*a^2*b^2*c/3 - 4*a^2*b*c^2/3 - a^2*c^3/9 + 7*a*b^4/9 - 4*a*b^2*c^2/3 + 5*a*c^4/9 + 5*b^4*c/9 - b^3*c^2/9 + b^2*c^3/9 + 7*b*c^4/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^3 * (c - a)^2 + (16/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (16/3 : ℝ) * a^3 * (b - c)^2 + (32/3 : ℝ) * a^2 * (c - a)^3 + (15 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (15 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (16/3 : ℝ) * a^2 * (b - c)^3 + (20/3 : ℝ) * a^1 * (c - a)^4 + (12 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (38/3 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (22/3 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (4/3 : ℝ) * a^1 * (b - c)^4 + (4/3 : ℝ) * (c - a)^5 + (26/9 : ℝ) * (c - a)^4 * (b - c)^1 + (28/9 : ℝ) * (c - a)^3 * (b - c)^2 + (19/9 : ℝ) * (c - a)^2 * (b - c)^3 + (5/9 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^4*b/9 + 7*a^4*c/9 - a^3*b^2/9 + a^3*c^2/9 + a^2*b^3/9 - 4*a^2*b^2*c/3 - 4*a^2*b*c^2/3 - a^2*c^3/9 + 7*a*b^4/9 - 4*a*b^2*c^2/3 + 5*a*c^4/9 + 5*b^4*c/9 - b^3*c^2/9 + b^2*c^3/9 + 7*b*c^4/9) := by
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
  have he : (a^4*b + a^4*c + a^3*b^2 + 2*a^3*b*c + a^3*c^2 + a^2*b^3 + 2*a^2*b^2*c + 2*a^2*b*c^2 - 4*a^2*b + a^2*c^3 - 2*a^2*c + a*b^4 + 2*a*b^3*c + 2*a*b^2*c^2 - 2*a*b^2 + 2*a*b*c^3 - 6*a*b*c + a*c^4 - 4*a*c^2 + b^4*c + b^3*c^2 + b^2*c^3 - 4*b^2*c + b*c^4 - 2*b*c^2) = (5*a^4*b/9 + 7*a^4*c/9 - a^3*b^2/9 + a^3*c^2/9 + a^2*b^3/9 - 4*a^2*b^2*c/3 - 4*a^2*b*c^2/3 - a^2*c^3/9 + 7*a*b^4/9 - 4*a*b^2*c^2/3 + 5*a*c^4/9 + 5*b^4*c/9 - b^3*c^2/9 + b^2*c^3/9 + 7*b*c^4/9) := by
    linear_combination (4*a^3*b/9 + 2*a^3*c/9 + 2*a^2*b^2/3 + 4*a^2*b*c/3 + 4*a^2*b/3 + 2*a^2*c^2/3 + 2*a^2*c/3 + 2*a*b^3/9 + 4*a*b^2*c/3 + 2*a*b^2/3 + 4*a*b*c^2/3 + 2*a*b*c + 4*a*c^3/9 + 4*a*c^2/3 + 4*b^3*c/9 + 2*b^2*c^2/3 + 4*b^2*c/3 + 2*b*c^3/9 + 2*b*c^2/3) * hab
  have hn : 0 ≤ (a^4*b + a^4*c + a^3*b^2 + 2*a^3*b*c + a^3*c^2 + a^2*b^3 + 2*a^2*b^2*c + 2*a^2*b*c^2 - 4*a^2*b + a^2*c^3 - 2*a^2*c + a*b^4 + 2*a*b^3*c + 2*a*b^2*c^2 - 2*a*b^2 + 2*a*b*c^3 - 6*a*b*c + a*c^4 - 4*a*c^2 + b^4*c + b^3*c^2 + b^2*c^3 - 4*b^2*c + b*c^4 - 2*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (2 * a / (a + b) + 2 * b / (b + c) + 2 * c / (c + a)) ≤ a ^ 2 + b ^ 2 + c ^ 2) := @solution
#print axioms solution
