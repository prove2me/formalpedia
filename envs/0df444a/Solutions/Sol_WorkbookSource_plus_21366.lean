-- Prove2me | solution 1 for WorkbookSource.plus_21366
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:17.084466+00:00
-- url     : https://prove2.me/submissions/c1218a63-8834-4943-b1da-9cba885ddf8f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 / b + b^2 / c + c^2 / a + 3 * a * b * c ≥ 6   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*c/9 + 2*a^4*c^2/9 + a^3*b^3/9 - 5*a^3*b^2*c/9 - 4*a^3*b*c^2/9 + a^3*c^3/9 + 2*a^2*b^4/9 - 4*a^2*b^3*c/9 + 5*a^2*b^2*c^2/3 - 5*a^2*b*c^3/9 + a*b^5/9 - 5*a*b^3*c^2/9 - 4*a*b^2*c^3/9 + b^3*c^3/9 + 2*b^2*c^4/9 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * a^4 * (b - a)^2 + (1 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1 : ℝ) * a^4 * (c - b)^2 + (25/9 : ℝ) * a^3 * (b - a)^3 + (17/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (16/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (11/9 : ℝ) * a^3 * (c - b)^3 + (28/9 : ℝ) * a^2 * (b - a)^4 + (83/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (11 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (44/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (7/9 : ℝ) * a^2 * (c - b)^4 + (16/9 : ℝ) * a^1 * (b - a)^5 + (58/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (83/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (53/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (14/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1/9 : ℝ) * a^1 * (c - b)^5 + (4/9 : ℝ) * (b - a)^6 + (16/9 : ℝ) * (b - a)^5 * (c - b)^1 + (25/9 : ℝ) * (b - a)^4 * (c - b)^2 + (19/9 : ℝ) * (b - a)^3 * (c - b)^3 + (7/9 : ℝ) * (b - a)^2 * (c - b)^4 + (1/9 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*c/9 + 2*a^4*c^2/9 + a^3*b^3/9 - 5*a^3*b^2*c/9 - 4*a^3*b*c^2/9 + a^3*c^3/9 + 2*a^2*b^4/9 - 4*a^2*b^3*c/9 + 5*a^2*b^2*c^2/3 - 5*a^2*b*c^3/9 + a*b^5/9 - 5*a*b^3*c^2/9 - 4*a*b^2*c^3/9 + b^3*c^3/9 + 2*b^2*c^4/9 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * a^4 * (c - a)^2 + (1 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (1 : ℝ) * a^4 * (b - c)^2 + (25/9 : ℝ) * a^3 * (c - a)^3 + (8/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (7/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (11/9 : ℝ) * a^3 * (b - c)^3 + (28/9 : ℝ) * a^2 * (c - a)^4 + (29/9 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (2 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (17/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (7/9 : ℝ) * a^2 * (b - c)^4 + (16/9 : ℝ) * a^1 * (c - a)^5 + (22/9 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (11/9 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (8/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (5/9 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1/9 : ℝ) * a^1 * (b - c)^5 + (4/9 : ℝ) * (c - a)^6 + (8/9 : ℝ) * (c - a)^5 * (b - c)^1 + (5/9 : ℝ) * (c - a)^4 * (b - c)^2 + (1/9 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*c/9 + 2*a^4*c^2/9 + a^3*b^3/9 - 5*a^3*b^2*c/9 - 4*a^3*b*c^2/9 + a^3*c^3/9 + 2*a^2*b^4/9 - 4*a^2*b^3*c/9 + 5*a^2*b^2*c^2/3 - 5*a^2*b*c^3/9 + a*b^5/9 - 5*a*b^3*c^2/9 - 4*a*b^2*c^3/9 + b^3*c^3/9 + 2*b^2*c^4/9 + b*c^5/9) := by
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
  have he : (a^3*c + 3*a^2*b^2*c^2 + a*b^3 - 6*a*b*c + b*c^3) = (a^5*c/9 + 2*a^4*c^2/9 + a^3*b^3/9 - 5*a^3*b^2*c/9 - 4*a^3*b*c^2/9 + a^3*c^3/9 + 2*a^2*b^4/9 - 4*a^2*b^3*c/9 + 5*a^2*b^2*c^2/3 - 5*a^2*b*c^3/9 + a*b^5/9 - 5*a*b^3*c^2/9 - 4*a*b^2*c^3/9 + b^3*c^3/9 + 2*b^2*c^4/9 + b*c^5/9) := by
    linear_combination (-a^4*c/9 + a^3*b*c/9 - a^3*c^2/9 - a^3*c/3 - a^2*b^3/9 + 4*a^2*b^2*c/9 + 4*a^2*b*c^2/9 + 2*a^2*b*c/3 - a*b^4/9 + a*b^3*c/9 - a*b^3/3 + 4*a*b^2*c^2/9 + 2*a*b^2*c/3 + a*b*c^3/9 + 2*a*b*c^2/3 + 2*a*b*c - b^2*c^3/9 - b*c^4/9 - b*c^3/3) * habc
  have hn : 0 ≤ (a^3*c + 3*a^2*b^2*c^2 + a*b^3 - 6*a*b*c + b*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a^2 / b + b^2 / c + c^2 / a + 3 * a * b * c ≥ 6) := @solution
#print axioms solution
