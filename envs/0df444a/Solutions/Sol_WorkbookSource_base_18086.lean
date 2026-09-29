-- Prove2me | solution 1 for WorkbookSource.base_18086
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:13:38.269782+00:00
-- url     : https://prove2.me/submissions/a2c12b1d-2590-4019-9e03-e9fd01e420b4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 + b * c) / (b + a * c) + (b^2 + a * c) / (c + b * a) + (c^2 + a * b) / (a + c * b) ≥ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b/3 + a^5*c/9 - 4*a^4*b*c/9 + 2*a^4*c^2/9 - 2*a^3*b^3/9 + 10*a^3*b^2*c/9 - 4*a^3*b*c^2/9 - 2*a^3*c^3/9 + 2*a^2*b^4/9 - 4*a^2*b^3*c/9 - 2*a^2*b^2*c^2 + 10*a^2*b*c^3/9 + a*b^5/9 - 4*a*b^4*c/9 + 10*a*b^3*c^2/9 - 4*a*b^2*c^3/9 - 4*a*b*c^4/9 + a*c^5/3 + b^5*c/3 - 2*b^3*c^3/9 + 2*b^2*c^4/9 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8/3 : ℝ) * a^4 * (b - a)^2 + (8/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8/3 : ℝ) * a^4 * (c - b)^2 + (62/9 : ℝ) * a^3 * (b - a)^3 + (28/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (10 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (34/9 : ℝ) * a^3 * (c - b)^3 + (20/3 : ℝ) * a^2 * (b - a)^4 + (34/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (40/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (26/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^2 * (c - b)^4 + (26/9 : ℝ) * a^1 * (b - a)^5 + (53/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (68/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (58/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (25/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/9 : ℝ) * a^1 * (c - b)^5 + (4/9 : ℝ) * (b - a)^6 + (10/9 : ℝ) * (b - a)^5 * (c - b)^1 + (16/9 : ℝ) * (b - a)^4 * (c - b)^2 + (16/9 : ℝ) * (b - a)^3 * (c - b)^3 + (7/9 : ℝ) * (b - a)^2 * (c - b)^4 + (1/9 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b/3 + a^5*c/9 - 4*a^4*b*c/9 + 2*a^4*c^2/9 - 2*a^3*b^3/9 + 10*a^3*b^2*c/9 - 4*a^3*b*c^2/9 - 2*a^3*c^3/9 + 2*a^2*b^4/9 - 4*a^2*b^3*c/9 - 2*a^2*b^2*c^2 + 10*a^2*b*c^3/9 + a*b^5/9 - 4*a*b^4*c/9 + 10*a*b^3*c^2/9 - 4*a*b^2*c^3/9 - 4*a*b*c^4/9 + a*c^5/3 + b^5*c/3 - 2*b^3*c^3/9 + 2*b^2*c^4/9 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8/3 : ℝ) * a^4 * (c - a)^2 + (8/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (8/3 : ℝ) * a^4 * (b - c)^2 + (62/9 : ℝ) * a^3 * (c - a)^3 + (34/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (12 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (34/9 : ℝ) * a^3 * (b - c)^3 + (20/3 : ℝ) * a^2 * (c - a)^4 + (46/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (58/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (32/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (2 : ℝ) * a^2 * (b - c)^4 + (26/9 : ℝ) * a^1 * (c - a)^5 + (77/9 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (116/9 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (88/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (31/9 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4/9 : ℝ) * a^1 * (b - c)^5 + (4/9 : ℝ) * (c - a)^6 + (14/9 : ℝ) * (c - a)^5 * (b - c)^1 + (26/9 : ℝ) * (c - a)^4 * (b - c)^2 + (28/9 : ℝ) * (c - a)^3 * (b - c)^3 + (5/3 : ℝ) * (c - a)^2 * (b - c)^4 + (1/3 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b/3 + a^5*c/9 - 4*a^4*b*c/9 + 2*a^4*c^2/9 - 2*a^3*b^3/9 + 10*a^3*b^2*c/9 - 4*a^3*b*c^2/9 - 2*a^3*c^3/9 + 2*a^2*b^4/9 - 4*a^2*b^3*c/9 - 2*a^2*b^2*c^2 + 10*a^2*b*c^3/9 + a*b^5/9 - 4*a*b^4*c/9 + 10*a*b^3*c^2/9 - 4*a*b^2*c^3/9 - 4*a*b*c^4/9 + a*c^5/3 + b^5*c/3 - 2*b^3*c^3/9 + 2*b^2*c^4/9 + b*c^5/9) := by
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
  have he : (a^4*b + 2*a^3*b^2*c - 3*a^3*b*c + a^3*c^2 + a^3*c + a^2*b^3 - 3*a^2*b^2*c^2 + 2*a^2*b^2*c - 3*a^2*b^2 + 2*a^2*b*c^3 + 2*a^2*b*c^2 + a^2*b*c - 3*a^2*c^2 + 2*a*b^3*c^2 - 3*a*b^3*c + a*b^3 + 2*a*b^2*c^2 + a*b^2*c - 3*a*b*c^3 + a*b*c^2 - 3*a*b*c + a*c^4 + b^4*c + b^2*c^3 - 3*b^2*c^2 + b*c^3) = (a^5*b/3 + a^5*c/9 - 4*a^4*b*c/9 + 2*a^4*c^2/9 - 2*a^3*b^3/9 + 10*a^3*b^2*c/9 - 4*a^3*b*c^2/9 - 2*a^3*c^3/9 + 2*a^2*b^4/9 - 4*a^2*b^3*c/9 - 2*a^2*b^2*c^2 + 10*a^2*b*c^3/9 + a*b^5/9 - 4*a*b^4*c/9 + 10*a*b^3*c^2/9 - 4*a*b^2*c^3/9 - 4*a*b*c^4/9 + a*c^5/3 + b^5*c/3 - 2*b^3*c^3/9 + 2*b^2*c^4/9 + b*c^5/9) := by
    linear_combination (-a^4*b/3 - a^4*c/9 + a^3*b^2/3 + 8*a^3*b*c/9 - a^3*c^2/9 - a^3*c/3 - a^2*b^3/9 - a^2*b^2*c/3 + a^2*b^2 - a^2*b*c^2/3 + a^2*c^3/3 + a^2*c^2 - a*b^4/9 + 8*a*b^3*c/9 - a*b^3/3 - a*b^2*c^2/3 + 8*a*b*c^3/9 + a*b*c - a*c^4/3 - b^4*c/3 + b^3*c^2/3 - b^2*c^3/9 + b^2*c^2 - b*c^4/9 - b*c^3/3) * hab
  have hn : 0 ≤ (a^4*b + 2*a^3*b^2*c - 3*a^3*b*c + a^3*c^2 + a^3*c + a^2*b^3 - 3*a^2*b^2*c^2 + 2*a^2*b^2*c - 3*a^2*b^2 + 2*a^2*b*c^3 + 2*a^2*b*c^2 + a^2*b*c - 3*a^2*c^2 + 2*a*b^3*c^2 - 3*a*b^3*c + a*b^3 + 2*a*b^2*c^2 + a*b^2*c - 3*a*b*c^3 + a*b*c^2 - 3*a*b*c + a*c^4 + b^4*c + b^2*c^3 - 3*b^2*c^2 + b*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a^2 + b * c) / (b + a * c) + (b^2 + a * c) / (c + b * a) + (c^2 + a * b) / (a + c * b) ≥ 3) := @solution
#print axioms solution
