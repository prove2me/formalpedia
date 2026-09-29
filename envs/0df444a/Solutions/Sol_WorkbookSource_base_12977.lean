-- Prove2me | solution 1 for WorkbookSource.base_12977
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:03.71688+00:00
-- url     : https://prove2.me/submissions/f82a892c-6a63-4e75-b253-318e664a6772

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (b * (1 - a) / (a * (1 + b)) + c * (1 - b) / (b * (1 + c)) + a * (1 - c) / (c * (1 + a))) ≥ 0  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b/27 + 2*a^4*b^2/9 + a^4*b*c/9 + 4*a^4*c^2/27 + a^3*b^3/3 + 4*a^3*b^2*c/27 + a^3*b*c^2/9 + a^3*c^3/3 + 4*a^2*b^4/27 + a^2*b^3*c/9 - 10*a^2*b^2*c^2/3 + 4*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^4*c/9 + 4*a*b^3*c^2/27 + a*b^2*c^3/9 + a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 + b^3*c^3/3 + 4*b^2*c^4/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (10/3 : ℝ) * a^4 * (b - a)^2 + (10/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (10/3 : ℝ) * a^4 * (c - b)^2 + (91/9 : ℝ) * a^3 * (b - a)^3 + (44/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (11 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (29/9 : ℝ) * a^3 * (c - b)^3 + (11 : ℝ) * a^2 * (b - a)^4 + (21 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (47/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (17/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2/3 : ℝ) * a^2 * (c - b)^4 + (134/27 : ℝ) * a^1 * (b - a)^5 + (317/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (269/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (100/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (16/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1/27 : ℝ) * a^1 * (c - b)^5 + (20/27 : ℝ) * (b - a)^6 + (56/27 : ℝ) * (b - a)^5 * (c - b)^1 + (19/9 : ℝ) * (b - a)^4 * (c - b)^2 + (25/27 : ℝ) * (b - a)^3 * (c - b)^3 + (4/27 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b/27 + 2*a^4*b^2/9 + a^4*b*c/9 + 4*a^4*c^2/27 + a^3*b^3/3 + 4*a^3*b^2*c/27 + a^3*b*c^2/9 + a^3*c^3/3 + 4*a^2*b^4/27 + a^2*b^3*c/9 - 10*a^2*b^2*c^2/3 + 4*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^4*c/9 + 4*a*b^3*c^2/27 + a*b^2*c^3/9 + a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 + b^3*c^3/3 + 4*b^2*c^4/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (10/3 : ℝ) * a^4 * (c - a)^2 + (10/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (10/3 : ℝ) * a^4 * (b - c)^2 + (91/9 : ℝ) * a^3 * (c - a)^3 + (47/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (12 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (29/9 : ℝ) * a^3 * (b - c)^3 + (11 : ℝ) * a^2 * (c - a)^4 + (23 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (56/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (20/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (2/3 : ℝ) * a^2 * (b - c)^4 + (134/27 : ℝ) * a^1 * (c - a)^5 + (353/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (341/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (145/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (25/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1/27 : ℝ) * a^1 * (b - c)^5 + (20/27 : ℝ) * (c - a)^6 + (64/27 : ℝ) * (c - a)^5 * (b - c)^1 + (77/27 : ℝ) * (c - a)^4 * (b - c)^2 + (43/27 : ℝ) * (c - a)^3 * (b - c)^3 + (11/27 : ℝ) * (c - a)^2 * (b - c)^4 + (1/27 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b/27 + 2*a^4*b^2/9 + a^4*b*c/9 + 4*a^4*c^2/27 + a^3*b^3/3 + 4*a^3*b^2*c/27 + a^3*b*c^2/9 + a^3*c^3/3 + 4*a^2*b^4/27 + a^2*b^3*c/9 - 10*a^2*b^2*c^2/3 + 4*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^4*c/9 + 4*a*b^3*c^2/27 + a*b^2*c^3/9 + a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 + b^3*c^3/3 + 4*b^2*c^4/27) := by
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
  have he : (-3*a^2*b^2*c^2 - a^2*b^2*c + a^2*b^2 - a^2*b*c^2 + a^2*b + a^2*c^2 - a*b^2*c^2 + a*c^2 + b^2*c^2 + b^2*c) = (a^5*b/27 + 2*a^4*b^2/9 + a^4*b*c/9 + 4*a^4*c^2/27 + a^3*b^3/3 + 4*a^3*b^2*c/27 + a^3*b*c^2/9 + a^3*c^3/3 + 4*a^2*b^4/27 + a^2*b^3*c/9 - 10*a^2*b^2*c^2/3 + 4*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^4*c/9 + 4*a*b^3*c^2/27 + a*b^2*c^3/9 + a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 + b^3*c^3/3 + 4*b^2*c^4/27) := by
    linear_combination (-a^4*b/27 - 5*a^3*b^2/27 - 2*a^3*b*c/27 - a^3*b/9 - 4*a^3*c^2/27 - 4*a^2*b^3/27 + a^2*b^2*c/9 - 4*a^2*b^2/9 + a^2*b*c^2/9 - a^2*b*c/9 - a^2*b/3 - 5*a^2*c^3/27 - 4*a^2*c^2/9 - 2*a*b^3*c/27 + a*b^2*c^2/9 - a*b^2*c/9 - 2*a*b*c^3/27 - a*b*c^2/9 - a*c^4/27 - a*c^3/9 - a*c^2/3 - b^4*c/27 - 5*b^3*c^2/27 - b^3*c/9 - 4*b^2*c^3/27 - 4*b^2*c^2/9 - b^2*c/3) * hab
  have hn : 0 ≤ (-3*a^2*b^2*c^2 - a^2*b^2*c + a^2*b^2 - a^2*b*c^2 + a^2*b + a^2*c^2 - a*b^2*c^2 + a*c^2 + b^2*c^2 + b^2*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (b * (1 - a) / (a * (1 + b)) + c * (1 - b) / (b * (1 + c)) + a * (1 - c) / (c * (1 + a))) ≥ 0) := @solution
#print axioms solution
