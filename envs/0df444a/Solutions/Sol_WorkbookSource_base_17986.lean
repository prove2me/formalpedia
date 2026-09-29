-- Prove2me | solution 1 for WorkbookSource.base_17986
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:13:35.982399+00:00
-- url     : https://prove2.me/submissions/501e8530-0e3b-49ea-878f-c80cd055e70f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : a / b + b / c + c / a + a * b * c ≥ 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*c/27 + a^4*b^2/27 - a^4*b*c/27 + a^4*c^2/9 + a^3*b^3/9 - 2*a^3*b^2*c/9 - 5*a^3*b*c^2/27 + a^3*c^3/9 + a^2*b^4/9 - 5*a^2*b^3*c/27 + 4*a^2*b^2*c^2/9 - 2*a^2*b*c^3/9 + a^2*c^4/27 + a*b^5/27 - a*b^4*c/27 - 2*a*b^3*c^2/9 - 5*a*b^2*c^3/27 - a*b*c^4/27 + b^4*c^2/27 + b^3*c^3/9 + b^2*c^4/9 + b*c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * a^4 * (b - a)^2 + (2/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (2/3 : ℝ) * a^4 * (c - b)^2 + (55/27 : ℝ) * a^3 * (b - a)^3 + (32/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (25/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (17/27 : ℝ) * a^3 * (c - b)^3 + (65/27 : ℝ) * a^2 * (b - a)^4 + (157/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (49/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (55/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (8/27 : ℝ) * a^2 * (c - b)^4 + (4/3 : ℝ) * a^1 * (b - a)^5 + (4 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (125/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (22/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (5/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1/27 : ℝ) * a^1 * (c - b)^5 + (8/27 : ℝ) * (b - a)^6 + (28/27 : ℝ) * (b - a)^5 * (c - b)^1 + (38/27 : ℝ) * (b - a)^4 * (c - b)^2 + (25/27 : ℝ) * (b - a)^3 * (c - b)^3 + (8/27 : ℝ) * (b - a)^2 * (c - b)^4 + (1/27 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*c/27 + a^4*b^2/27 - a^4*b*c/27 + a^4*c^2/9 + a^3*b^3/9 - 2*a^3*b^2*c/9 - 5*a^3*b*c^2/27 + a^3*c^3/9 + a^2*b^4/9 - 5*a^2*b^3*c/27 + 4*a^2*b^2*c^2/9 - 2*a^2*b*c^3/9 + a^2*c^4/27 + a*b^5/27 - a*b^4*c/27 - 2*a*b^3*c^2/9 - 5*a*b^2*c^3/27 - a*b*c^4/27 + b^4*c^2/27 + b^3*c^3/9 + b^2*c^4/9 + b*c^5/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * a^4 * (c - a)^2 + (2/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (2/3 : ℝ) * a^4 * (b - c)^2 + (55/27 : ℝ) * a^3 * (c - a)^3 + (23/9 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (16/9 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (17/27 : ℝ) * a^3 * (b - c)^3 + (65/27 : ℝ) * a^2 * (c - a)^4 + (103/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (22/9 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (28/27 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (8/27 : ℝ) * a^2 * (b - c)^4 + (4/3 : ℝ) * a^1 * (c - a)^5 + (8/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (53/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (7/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2/9 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1/27 : ℝ) * a^1 * (b - c)^5 + (8/27 : ℝ) * (c - a)^6 + (20/27 : ℝ) * (c - a)^5 * (b - c)^1 + (2/3 : ℝ) * (c - a)^4 * (b - c)^2 + (7/27 : ℝ) * (c - a)^3 * (b - c)^3 + (1/27 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*c/27 + a^4*b^2/27 - a^4*b*c/27 + a^4*c^2/9 + a^3*b^3/9 - 2*a^3*b^2*c/9 - 5*a^3*b*c^2/27 + a^3*c^3/9 + a^2*b^4/9 - 5*a^2*b^3*c/27 + 4*a^2*b^2*c^2/9 - 2*a^2*b*c^3/9 + a^2*c^4/27 + a*b^5/27 - a*b^4*c/27 - 2*a*b^3*c^2/9 - 5*a*b^2*c^3/27 - a*b*c^4/27 + b^4*c^2/27 + b^3*c^3/9 + b^2*c^4/9 + b*c^5/27) := by
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
  have he : (a^2*b^2*c^2 + a^2*c + a*b^2 - 4*a*b*c + b*c^2) = (a^5*c/27 + a^4*b^2/27 - a^4*b*c/27 + a^4*c^2/9 + a^3*b^3/9 - 2*a^3*b^2*c/9 - 5*a^3*b*c^2/27 + a^3*c^3/9 + a^2*b^4/9 - 5*a^2*b^3*c/27 + 4*a^2*b^2*c^2/9 - 2*a^2*b*c^3/9 + a^2*c^4/27 + a*b^5/27 - a*b^4*c/27 - 2*a*b^3*c^2/9 - 5*a*b^2*c^3/27 - a*b*c^4/27 + b^4*c^2/27 + b^3*c^3/9 + b^2*c^4/9 + b*c^5/27) := by
    linear_combination (-a^4*c/27 - a^3*b^2/27 + 2*a^3*b*c/27 - 2*a^3*c^2/27 - a^3*c/9 - 2*a^2*b^3/27 + 5*a^2*b^2*c/27 - a^2*b^2/9 + 5*a^2*b*c^2/27 + a^2*b*c/3 - a^2*c^3/27 - a^2*c^2/9 - a^2*c/3 - a*b^4/27 + 2*a*b^3*c/27 - a*b^3/9 + 5*a*b^2*c^2/27 + a*b^2*c/3 - a*b^2/3 + 2*a*b*c^3/27 + a*b*c^2/3 + 4*a*b*c/3 - b^3*c^2/27 - 2*b^2*c^3/27 - b^2*c^2/9 - b*c^4/27 - b*c^3/9 - b*c^2/3) * hab
  have hn : 0 ≤ (a^2*b^2*c^2 + a^2*c + a*b^2 - 4*a*b*c + b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3), a / b + b / c + c / a + a * b * c ≥ 4) := @solution
#print axioms solution
