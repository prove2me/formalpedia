-- Prove2me | solution 1 for WorkbookSource.plus_54627
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:51.451238+00:00
-- url     : https://prove2.me/submissions/786b35ca-37ed-46dd-ad7f-b955c962a83c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^2 + b^2 + c^2 + 3 * a * b * c ≥ 2 * (a * b + b * c + c * a) + (1 / 6) * a * b * c * (1 - a * b * c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6/27 + 4*a^5*b/27 + 4*a^5*c/27 - 2*a^4*b^2/27 + 5*a^4*b*c/27 - 2*a^4*c^2/27 - 8*a^3*b^3/27 - 5*a^3*b^2*c/27 - 5*a^3*b*c^2/27 - 8*a^3*c^3/27 - 2*a^2*b^4/27 - 5*a^2*b^3*c/27 + 7*a^2*b^2*c^2/9 - 5*a^2*b*c^3/27 - 2*a^2*c^4/27 + 4*a*b^5/27 + 5*a*b^4*c/27 - 5*a*b^3*c^2/27 - 5*a*b^2*c^3/27 + 5*a*b*c^4/27 + 4*a*c^5/27 + 2*b^6/27 + 4*b^5*c/27 - 2*b^4*c^2/27 - 8*b^3*c^3/27 - 2*b^2*c^4/27 + 4*b*c^5/27 + 2*c^6/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5/3 : ℝ) * a^4 * (b - a)^2 + (5/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (5/3 : ℝ) * a^4 * (c - b)^2 + (82/27 : ℝ) * a^3 * (b - a)^3 + (41/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (79/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (98/27 : ℝ) * a^3 * (c - b)^3 + (47/27 : ℝ) * a^2 * (b - a)^4 + (94/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (112/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (289/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (71/27 : ℝ) * a^2 * (c - b)^4 + (8/27 : ℝ) * a^1 * (b - a)^5 + (20/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (178/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (247/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (121/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (20/27 : ℝ) * a^1 * (c - b)^5 + (32/27 : ℝ) * (b - a)^4 * (c - b)^2 + (64/27 : ℝ) * (b - a)^3 * (c - b)^3 + (16/9 : ℝ) * (b - a)^2 * (c - b)^4 + (16/27 : ℝ) * (b - a)^1 * (c - b)^5 + (2/27 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6/27 + 4*a^5*b/27 + 4*a^5*c/27 - 2*a^4*b^2/27 + 5*a^4*b*c/27 - 2*a^4*c^2/27 - 8*a^3*b^3/27 - 5*a^3*b^2*c/27 - 5*a^3*b*c^2/27 - 8*a^3*c^3/27 - 2*a^2*b^4/27 - 5*a^2*b^3*c/27 + 7*a^2*b^2*c^2/9 - 5*a^2*b*c^3/27 - 2*a^2*c^4/27 + 4*a*b^5/27 + 5*a*b^4*c/27 - 5*a*b^3*c^2/27 - 5*a*b^2*c^3/27 + 5*a*b*c^4/27 + 4*a*c^5/27 + 2*b^6/27 + 4*b^5*c/27 - 2*b^4*c^2/27 - 8*b^3*c^3/27 - 2*b^2*c^4/27 + 4*b*c^5/27 + 2*c^6/27) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (a^2*b^2*c^2 + 6*a^2 + 17*a*b*c - 12*a*b - 12*a*c + 6*b^2 - 12*b*c + 6*c^2) = (2*a^6/27 + 4*a^5*b/27 + 4*a^5*c/27 - 2*a^4*b^2/27 + 5*a^4*b*c/27 - 2*a^4*c^2/27 - 8*a^3*b^3/27 - 5*a^3*b^2*c/27 - 5*a^3*b*c^2/27 - 8*a^3*c^3/27 - 2*a^2*b^4/27 - 5*a^2*b^3*c/27 + 7*a^2*b^2*c^2/9 - 5*a^2*b*c^3/27 - 2*a^2*c^4/27 + 4*a*b^5/27 + 5*a*b^4*c/27 - 5*a*b^3*c^2/27 - 5*a*b^2*c^3/27 + 5*a*b*c^4/27 + 4*a*c^5/27 + 2*b^6/27 + 4*b^5*c/27 - 2*b^4*c^2/27 - 8*b^3*c^3/27 - 2*b^2*c^4/27 + 4*b*c^5/27 + 2*c^6/27) := by
    linear_combination (-2*a^5/27 - 2*a^4*b/27 - 2*a^4*c/27 - 2*a^4/9 + 4*a^3*b^2/27 - a^3*b*c/27 + 4*a^3*c^2/27 - 2*a^3/3 + 4*a^2*b^3/27 + 2*a^2*b^2*c/27 + 4*a^2*b^2/9 + 2*a^2*b*c^2/27 - a^2*b*c/9 + 2*a^2*b/3 + 4*a^2*c^3/27 + 4*a^2*c^2/9 + 2*a^2*c/3 - 2*a^2 - 2*a*b^4/27 - a*b^3*c/27 + 2*a*b^2*c^2/27 - a*b^2*c/9 + 2*a*b^2/3 - a*b*c^3/27 - a*b*c^2/9 - 5*a*b*c/3 + 4*a*b - 2*a*c^4/27 + 2*a*c^2/3 + 4*a*c - 2*b^5/27 - 2*b^4*c/27 - 2*b^4/9 + 4*b^3*c^2/27 - 2*b^3/3 + 4*b^2*c^3/27 + 4*b^2*c^2/9 + 2*b^2*c/3 - 2*b^2 - 2*b*c^4/27 + 2*b*c^2/3 + 4*b*c - 2*c^5/27 - 2*c^4/9 - 2*c^3/3 - 2*c^2) * hab
  have hn : 0 ≤ (a^2*b^2*c^2 + 6*a^2 + 17*a*b*c - 12*a*b - 12*a*c + 6*b^2 - 12*b*c + 6*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a^2 + b^2 + c^2 + 3 * a * b * c ≥ 2 * (a * b + b * c + c * a) + (1 / 6) * a * b * c * (1 - a * b * c)) := @solution
#print axioms solution
