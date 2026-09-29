-- Prove2me | solution 1 for WorkbookSource.plus_3424
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:16:02.21575+00:00
-- url     : https://prove2.me/submissions/b22304b4-7fb7-4dd9-883a-0c03a5ad537b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 / (2 * a * (a + 1) + c * a + b) + b^2 / (2 * b * (b + 1) + a * b + c) + c^2 / (2 * c * (c + 1) + b * c + a) ≤ 1 / 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (10*a^5*b/27 + 2*a^5*c/27 - 7*a^4*b^2/27 + 22*a^4*b*c/9 + 13*a^4*c^2/27 - 2*a^3*b^3/9 + 58*a^3*b^2*c/27 - 22*a^3*b*c^2/27 - 2*a^3*c^3/9 + 13*a^2*b^4/27 - 22*a^2*b^3*c/27 - 38*a^2*b^2*c^2/3 + 58*a^2*b*c^3/27 - 7*a^2*c^4/27 + 2*a*b^5/27 + 22*a*b^4*c/9 + 58*a*b^3*c^2/27 - 22*a*b^2*c^3/27 + 22*a*b*c^4/9 + 10*a*c^5/27 + 10*b^5*c/27 - 7*b^4*c^2/27 - 2*b^3*c^3/9 + 13*b^2*c^4/27 + 2*b*c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^4 * (c - b)^2 + (32 : ℝ) * a^3 * (b - a)^3 + (48 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (48 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (16 : ℝ) * a^3 * (c - b)^3 + (260/9 : ℝ) * a^2 * (b - a)^4 + (520/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (188/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (304/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (44/9 : ℝ) * a^2 * (c - b)^4 + (28/3 : ℝ) * a^1 * (b - a)^5 + (70/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (260/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (20 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/9 : ℝ) * a^1 * (c - b)^5 + (4/9 : ℝ) * (b - a)^6 + (40/27 : ℝ) * (b - a)^5 * (c - b)^1 + (73/27 : ℝ) * (b - a)^4 * (c - b)^2 + (22/9 : ℝ) * (b - a)^3 * (c - b)^3 + (23/27 : ℝ) * (b - a)^2 * (c - b)^4 + (2/27 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (10*a^5*b/27 + 2*a^5*c/27 - 7*a^4*b^2/27 + 22*a^4*b*c/9 + 13*a^4*c^2/27 - 2*a^3*b^3/9 + 58*a^3*b^2*c/27 - 22*a^3*b*c^2/27 - 2*a^3*c^3/9 + 13*a^2*b^4/27 - 22*a^2*b^3*c/27 - 38*a^2*b^2*c^2/3 + 58*a^2*b*c^3/27 - 7*a^2*c^4/27 + 2*a*b^5/27 + 22*a*b^4*c/9 + 58*a*b^3*c^2/27 - 22*a*b^2*c^3/27 + 22*a*b*c^4/9 + 10*a*c^5/27 + 10*b^5*c/27 - 7*b^4*c^2/27 - 2*b^3*c^3/9 + 13*b^2*c^4/27 + 2*b*c^5/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (c - a)^2 + (12 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (12 : ℝ) * a^4 * (b - c)^2 + (32 : ℝ) * a^3 * (c - a)^3 + (48 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (48 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (16 : ℝ) * a^3 * (b - c)^3 + (260/9 : ℝ) * a^2 * (c - a)^4 + (520/9 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (188/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (304/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (44/9 : ℝ) * a^2 * (b - c)^4 + (28/3 : ℝ) * a^1 * (c - a)^5 + (70/3 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (260/9 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (20 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (6 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4/9 : ℝ) * a^1 * (b - c)^5 + (4/9 : ℝ) * (c - a)^6 + (32/27 : ℝ) * (c - a)^5 * (b - c)^1 + (53/27 : ℝ) * (c - a)^4 * (b - c)^2 + (22/9 : ℝ) * (c - a)^3 * (b - c)^3 + (43/27 : ℝ) * (c - a)^2 * (b - c)^4 + (10/27 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*a^5*b/27 + 2*a^5*c/27 - 7*a^4*b^2/27 + 22*a^4*b*c/9 + 13*a^4*c^2/27 - 2*a^3*b^3/9 + 58*a^3*b^2*c/27 - 22*a^3*b*c^2/27 - 2*a^3*c^3/9 + 13*a^2*b^4/27 - 22*a^2*b^3*c/27 - 38*a^2*b^2*c^2/3 + 58*a^2*b*c^3/27 - 7*a^2*c^4/27 + 2*a*b^5/27 + 22*a*b^4*c/9 + 58*a*b^3*c^2/27 - 22*a*b^2*c^3/27 + 22*a*b*c^4/9 + 10*a*c^5/27 + 10*b^5*c/27 - 7*b^4*c^2/27 - 2*b^3*c^3/9 + 13*b^2*c^4/27 + 2*b*c^5/27) := by
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
  have he : (-4*a^3*b^2 - 4*a^3*b*c^2 + a^3*b*c + 2*a^3*b - 4*a^2*b^3*c - 15*a^2*b^2*c^2 - 6*a^2*b^2*c + a^2*b^2 - 6*a^2*b*c^2 + 6*a^2*b*c + 4*a^2*b - 4*a^2*c^3 + a^2*c^2 + 2*a^2*c + a*b^3*c - 4*a*b^2*c^3 - 6*a*b^2*c^2 + 6*a*b^2*c + 2*a*b^2 + a*b*c^3 + 6*a*b*c^2 + 9*a*b*c + 2*a*c^3 + 4*a*c^2 - 4*b^3*c^2 + 2*b^3*c + b^2*c^2 + 4*b^2*c + 2*b*c^2) = (10*a^5*b/27 + 2*a^5*c/27 - 7*a^4*b^2/27 + 22*a^4*b*c/9 + 13*a^4*c^2/27 - 2*a^3*b^3/9 + 58*a^3*b^2*c/27 - 22*a^3*b*c^2/27 - 2*a^3*c^3/9 + 13*a^2*b^4/27 - 22*a^2*b^3*c/27 - 38*a^2*b^2*c^2/3 + 58*a^2*b*c^3/27 - 7*a^2*c^4/27 + 2*a*b^5/27 + 22*a*b^4*c/9 + 58*a*b^3*c^2/27 - 22*a*b^2*c^3/27 + 22*a*b*c^4/9 + 10*a*c^5/27 + 10*b^5*c/27 - 7*b^4*c^2/27 - 2*b^3*c^3/9 + 13*b^2*c^4/27 + 2*b*c^5/27) := by
    linear_combination (-10*a^4*b/27 - 2*a^4*c/27 + 17*a^3*b^2/27 - 2*a^3*b*c - 10*a^3*b/9 - 11*a^3*c^2/27 - 2*a^3*c/9 - 11*a^2*b^3/27 - 7*a^2*b^2*c/9 - a^2*b^2 - 7*a^2*b*c^2/9 - 11*a^2*b*c/3 - 4*a^2*b/3 + 17*a^2*c^3/27 - a^2*c^2 - 2*a^2*c/3 - 2*a*b^4/27 - 2*a*b^3*c - 2*a*b^3/9 - 7*a*b^2*c^2/9 - 11*a*b^2*c/3 - 2*a*b^2/3 - 2*a*b*c^3 - 11*a*b*c^2/3 - 3*a*b*c - 10*a*c^4/27 - 10*a*c^3/9 - 4*a*c^2/3 - 10*b^4*c/27 + 17*b^3*c^2/27 - 10*b^3*c/9 - 11*b^2*c^3/27 - b^2*c^2 - 4*b^2*c/3 - 2*b*c^4/27 - 2*b*c^3/9 - 2*b*c^2/3) * habc
  have hn : 0 ≤ (-4*a^3*b^2 - 4*a^3*b*c^2 + a^3*b*c + 2*a^3*b - 4*a^2*b^3*c - 15*a^2*b^2*c^2 - 6*a^2*b^2*c + a^2*b^2 - 6*a^2*b*c^2 + 6*a^2*b*c + 4*a^2*b - 4*a^2*c^3 + a^2*c^2 + 2*a^2*c + a*b^3*c - 4*a*b^2*c^3 - 6*a*b^2*c^2 + 6*a*b^2*c + 2*a*b^2 + a*b*c^3 + 6*a*b*c^2 + 9*a*b*c + 2*a*c^3 + 4*a*c^2 - 4*b^3*c^2 + 2*b^3*c + b^2*c^2 + 4*b^2*c + 2*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a^2 / (2 * a * (a + 1) + c * a + b) + b^2 / (2 * b * (b + 1) + a * b + c) + c^2 / (2 * c * (c + 1) + b * c + a) ≤ 1 / 2) := @solution
#print axioms solution
