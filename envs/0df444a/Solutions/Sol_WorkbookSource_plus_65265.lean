-- Prove2me | solution 1 for WorkbookSource.plus_65265
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:25.809516+00:00
-- url     : https://prove2.me/submissions/2cc968cc-58c4-464d-9d23-0b52b0ca9ec7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 3 * (1 / a + 1 / b + 1 / c - 1) ^ 2 + 1 ≥ 4 / (a * b * c) + 3 * (a / (b * c) + b / (c * a) + c / (a * b))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2/3 - 13*a^4*b*c/27 + a^4*c^2/3 + 2*a^3*b^3/3 - 7*a^3*b^2*c/9 - 7*a^3*b*c^2/9 + 2*a^3*c^3/3 + a^2*b^4/3 - 7*a^2*b^3*c/9 + 19*a^2*b^2*c^2/9 - 7*a^2*b*c^3/9 + a^2*c^4/3 - 13*a*b^4*c/27 - 7*a*b^3*c^2/9 - 7*a*b^2*c^3/9 - 13*a*b*c^4/27 + b^4*c^2/3 + 2*b^3*c^3/3 + b^2*c^4/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5/3 : ℝ) * a^4 * (b - a)^2 + (5/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (5/3 : ℝ) * a^4 * (c - b)^2 + (166/27 : ℝ) * a^3 * (b - a)^3 + (83/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (37/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (14/27 : ℝ) * a^3 * (c - b)^3 + (233/27 : ℝ) * a^2 * (b - a)^4 + (466/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (88/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (31/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (5/27 : ℝ) * a^2 * (c - b)^4 + (148/27 : ℝ) * a^1 * (b - a)^5 + (370/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (34/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (89/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (5/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/3 : ℝ) * (b - a)^6 + (4 : ℝ) * (b - a)^5 * (c - b)^1 + (13/3 : ℝ) * (b - a)^4 * (c - b)^2 + (2 : ℝ) * (b - a)^3 * (c - b)^3 + (1/3 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2/3 - 13*a^4*b*c/27 + a^4*c^2/3 + 2*a^3*b^3/3 - 7*a^3*b^2*c/9 - 7*a^3*b*c^2/9 + 2*a^3*c^3/3 + a^2*b^4/3 - 7*a^2*b^3*c/9 + 19*a^2*b^2*c^2/9 - 7*a^2*b*c^3/9 + a^2*c^4/3 - 13*a*b^4*c/27 - 7*a*b^3*c^2/9 - 7*a*b^2*c^3/9 - 13*a*b*c^4/27 + b^4*c^2/3 + 2*b^3*c^3/3 + b^2*c^4/3) := by
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
  have he : (-3*a^3*b*c + 4*a^2*b^2*c^2 - 6*a^2*b^2*c + 3*a^2*b^2 - 6*a^2*b*c^2 + 6*a^2*b*c + 3*a^2*c^2 - 3*a*b^3*c - 6*a*b^2*c^2 + 6*a*b^2*c - 3*a*b*c^3 + 6*a*b*c^2 - 4*a*b*c + 3*b^2*c^2) = (a^4*b^2/3 - 13*a^4*b*c/27 + a^4*c^2/3 + 2*a^3*b^3/3 - 7*a^3*b^2*c/9 - 7*a^3*b*c^2/9 + 2*a^3*c^3/3 + a^2*b^4/3 - 7*a^2*b^3*c/9 + 19*a^2*b^2*c^2/9 - 7*a^2*b*c^3/9 + a^2*c^4/3 - 13*a*b^4*c/27 - 7*a*b^3*c^2/9 - 7*a*b^2*c^3/9 - 13*a*b*c^4/27 + b^4*c^2/3 + 2*b^3*c^3/3 + b^2*c^4/3) := by
    linear_combination (-a^3*b^2/3 + 13*a^3*b*c/27 - a^3*c^2/3 - a^2*b^3/3 + 17*a^2*b^2*c/27 - a^2*b^2 + 17*a^2*b*c^2/27 - 14*a^2*b*c/9 - a^2*c^3/3 - a^2*c^2 + 13*a*b^3*c/27 + 17*a*b^2*c^2/27 - 14*a*b^2*c/9 + 13*a*b*c^3/27 - 14*a*b*c^2/9 + 4*a*b*c/3 - b^3*c^2/3 - b^2*c^3/3 - b^2*c^2) * hab
  have hn : 0 ≤ (-3*a^3*b*c + 4*a^2*b^2*c^2 - 6*a^2*b^2*c + 3*a^2*b^2 - 6*a^2*b*c^2 + 6*a^2*b*c + 3*a^2*c^2 - 3*a*b^3*c - 6*a*b^2*c^2 + 6*a*b^2*c - 3*a*b*c^3 + 6*a*b*c^2 - 4*a*b*c + 3*b^2*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), 3 * (1 / a + 1 / b + 1 / c - 1) ^ 2 + 1 ≥ 4 / (a * b * c) + 3 * (a / (b * c) + b / (c * a) + c / (a * b))) := @solution
#print axioms solution
