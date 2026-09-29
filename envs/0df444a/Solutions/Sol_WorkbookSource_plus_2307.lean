-- Prove2me | solution 1 for WorkbookSource.plus_2307
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:15:59.378068+00:00
-- url     : https://prove2.me/submissions/45fa42a1-ca24-459b-9f54-10e9ab849073

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (2 * a ^ 2 + a + 6) + 1 / (2 * b ^ 2 + b + 6) + 1 / (2 * c ^ 2 + c + 6) ≥ 1 / 3   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6/27 + 17*a^5*b/27 + 17*a^5*c/27 - 4*a^4*b^2/27 + 68*a^4*b*c/27 - 4*a^4*c^2/27 - 34*a^3*b^3/27 + 11*a^3*b^2*c/27 + 11*a^3*b*c^2/27 - 34*a^3*c^3/27 - 4*a^2*b^4/27 + 11*a^2*b^3*c/27 - 86*a^2*b^2*c^2/9 + 11*a^2*b*c^3/27 - 4*a^2*c^4/27 + 17*a*b^5/27 + 68*a*b^4*c/27 + 11*a*b^3*c^2/27 + 11*a*b^2*c^3/27 + 68*a*b*c^4/27 + 17*a*c^5/27 + 4*b^6/27 + 17*b^5*c/27 - 4*b^4*c^2/27 - 34*b^3*c^3/27 - 4*b^2*c^4/27 + 17*b*c^5/27 + 4*c^6/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (14 : ℝ) * a^4 * (b - a)^2 + (14 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (14 : ℝ) * a^4 * (c - b)^2 + (898/27 : ℝ) * a^3 * (b - a)^3 + (449/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (559/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (614/27 : ℝ) * a^3 * (c - b)^3 + (716/27 : ℝ) * a^2 * (b - a)^4 + (1432/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (739/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1501/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (290/27 : ℝ) * a^2 * (c - b)^4 + (64/9 : ℝ) * a^1 * (b - a)^5 + (160/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1022/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (39 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (145/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (58/27 : ℝ) * a^1 * (c - b)^5 + (100/27 : ℝ) * (b - a)^4 * (c - b)^2 + (200/27 : ℝ) * (b - a)^3 * (c - b)^3 + (47/9 : ℝ) * (b - a)^2 * (c - b)^4 + (41/27 : ℝ) * (b - a)^1 * (c - b)^5 + (4/27 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6/27 + 17*a^5*b/27 + 17*a^5*c/27 - 4*a^4*b^2/27 + 68*a^4*b*c/27 - 4*a^4*c^2/27 - 34*a^3*b^3/27 + 11*a^3*b^2*c/27 + 11*a^3*b*c^2/27 - 34*a^3*c^3/27 - 4*a^2*b^4/27 + 11*a^2*b^3*c/27 - 86*a^2*b^2*c^2/9 + 11*a^2*b*c^3/27 - 4*a^2*c^4/27 + 17*a*b^5/27 + 68*a*b^4*c/27 + 11*a*b^3*c^2/27 + 11*a*b^2*c^3/27 + 68*a*b*c^4/27 + 17*a*c^5/27 + 4*b^6/27 + 17*b^5*c/27 - 4*b^4*c^2/27 - 34*b^3*c^3/27 - 4*b^2*c^4/27 + 17*b*c^5/27 + 4*c^6/27) := by
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
  have he : (-8*a^2*b^2*c^2 - 4*a^2*b^2*c - 12*a^2*b^2 - 4*a^2*b*c^2 - 2*a^2*b*c - 6*a^2*b - 12*a^2*c^2 - 6*a^2*c - 4*a*b^2*c^2 - 2*a*b^2*c - 6*a*b^2 - 2*a*b*c^2 - a*b*c - 3*a*b - 6*a*c^2 - 3*a*c - 12*b^2*c^2 - 6*b^2*c - 6*b*c^2 - 3*b*c + 108) = (4*a^6/27 + 17*a^5*b/27 + 17*a^5*c/27 - 4*a^4*b^2/27 + 68*a^4*b*c/27 - 4*a^4*c^2/27 - 34*a^3*b^3/27 + 11*a^3*b^2*c/27 + 11*a^3*b*c^2/27 - 34*a^3*c^3/27 - 4*a^2*b^4/27 + 11*a^2*b^3*c/27 - 86*a^2*b^2*c^2/9 + 11*a^2*b*c^3/27 - 4*a^2*c^4/27 + 17*a*b^5/27 + 68*a*b^4*c/27 + 11*a*b^3*c^2/27 + 11*a*b^2*c^3/27 + 68*a*b*c^4/27 + 17*a*c^5/27 + 4*b^6/27 + 17*b^5*c/27 - 4*b^4*c^2/27 - 34*b^3*c^3/27 - 4*b^2*c^4/27 + 17*b*c^5/27 + 4*c^6/27) := by
    linear_combination (-4*a^5/27 - 13*a^4*b/27 - 13*a^4*c/27 - 4*a^4/9 + 17*a^3*b^2/27 - 14*a^3*b*c/9 - a^3*b + 17*a^3*c^2/27 - a^3*c - 4*a^3/3 + 17*a^2*b^3/27 + 14*a^2*b^2*c/27 + 26*a^2*b^2/9 + 14*a^2*b*c^2/27 - 8*a^2*b*c/3 - 5*a^2*b/3 + 17*a^2*c^3/27 + 26*a^2*c^2/9 - 5*a^2*c/3 - 4*a^2 - 13*a*b^4/27 - 14*a*b^3*c/9 - a*b^3 + 14*a*b^2*c^2/27 - 8*a*b^2*c/3 - 5*a*b^2/3 - 14*a*b*c^3/9 - 8*a*b*c^2/3 - 20*a*b*c/3 - 7*a*b - 13*a*c^4/27 - a*c^3 - 5*a*c^2/3 - 7*a*c - 12*a - 4*b^5/27 - 13*b^4*c/27 - 4*b^4/9 + 17*b^3*c^2/27 - b^3*c - 4*b^3/3 + 17*b^2*c^3/27 + 26*b^2*c^2/9 - 5*b^2*c/3 - 4*b^2 - 13*b*c^4/27 - b*c^3 - 5*b*c^2/3 - 7*b*c - 12*b - 4*c^5/27 - 4*c^4/9 - 4*c^3/3 - 4*c^2 - 12*c - 36) * hab
  have hn : 0 ≤ (-8*a^2*b^2*c^2 - 4*a^2*b^2*c - 12*a^2*b^2 - 4*a^2*b*c^2 - 2*a^2*b*c - 6*a^2*b - 12*a^2*c^2 - 6*a^2*c - 4*a*b^2*c^2 - 2*a*b^2*c - 6*a*b^2 - 2*a*b*c^2 - a*b*c - 3*a*b - 6*a*c^2 - 3*a*c - 12*b^2*c^2 - 6*b^2*c - 6*b*c^2 - 3*b*c + 108) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), 1 / (2 * a ^ 2 + a + 6) + 1 / (2 * b ^ 2 + b + 6) + 1 / (2 * c ^ 2 + c + 6) ≥ 1 / 3) := @solution
#print axioms solution
