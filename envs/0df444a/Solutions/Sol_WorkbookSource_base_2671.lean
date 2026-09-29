-- Prove2me | solution 1 for WorkbookSource.base_2671
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:03:13.415172+00:00
-- url     : https://prove2.me/submissions/378126f3-907c-4346-b108-87e8e9b431b4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a + 3 * b) / c + (b + 3 * c) / a + (c + 3 * a) / b ≥ 6 * (3 - a * b * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b/27 + a^5*c/9 + 2*a^4*b^2/9 - 2*a^4*b*c/9 + 10*a^4*c^2/27 + 4*a^3*b^3/9 - 29*a^3*b^2*c/27 - a^3*b*c^2 + 4*a^3*c^3/9 + 10*a^2*b^4/27 - a^2*b^3*c + 10*a^2*b^2*c^2/3 - 29*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^5/9 - 2*a*b^4*c/9 - 29*a*b^3*c^2/27 - a*b^2*c^3 - 2*a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 + 4*b^3*c^3/9 + 10*b^2*c^4/27 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^4 * (b - a)^2 + (2 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^4 * (c - b)^2 + (56/9 : ℝ) * a^3 * (b - a)^3 + (31/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (23/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (16/9 : ℝ) * a^3 * (c - b)^3 + (70/9 : ℝ) * a^2 * (b - a)^4 + (158/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (47/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (53/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (10/9 : ℝ) * a^2 * (c - b)^4 + (128/27 : ℝ) * a^1 * (b - a)^5 + (356/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (392/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (205/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (49/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/27 : ℝ) * a^1 * (c - b)^5 + (32/27 : ℝ) * (b - a)^6 + (104/27 : ℝ) * (b - a)^5 * (c - b)^1 + (44/9 : ℝ) * (b - a)^4 * (c - b)^2 + (82/27 : ℝ) * (b - a)^3 * (c - b)^3 + (25/27 : ℝ) * (b - a)^2 * (c - b)^4 + (1/9 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b/27 + a^5*c/9 + 2*a^4*b^2/9 - 2*a^4*b*c/9 + 10*a^4*c^2/27 + 4*a^3*b^3/9 - 29*a^3*b^2*c/27 - a^3*b*c^2 + 4*a^3*c^3/9 + 10*a^2*b^4/27 - a^2*b^3*c + 10*a^2*b^2*c^2/3 - 29*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^5/9 - 2*a*b^4*c/9 - 29*a*b^3*c^2/27 - a*b^2*c^3 - 2*a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 + 4*b^3*c^3/9 + 10*b^2*c^4/27 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^4 * (c - a)^2 + (2 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (2 : ℝ) * a^4 * (b - c)^2 + (56/9 : ℝ) * a^3 * (c - a)^3 + (25/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (17/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (16/9 : ℝ) * a^3 * (b - c)^3 + (70/9 : ℝ) * a^2 * (c - a)^4 + (122/9 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (29/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (35/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (10/9 : ℝ) * a^2 * (b - c)^4 + (128/27 : ℝ) * a^1 * (c - a)^5 + (284/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (248/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (115/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (31/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4/27 : ℝ) * a^1 * (b - c)^5 + (32/27 : ℝ) * (c - a)^6 + (88/27 : ℝ) * (c - a)^5 * (b - c)^1 + (92/27 : ℝ) * (c - a)^4 * (b - c)^2 + (46/27 : ℝ) * (c - a)^3 * (b - c)^3 + (11/27 : ℝ) * (c - a)^2 * (b - c)^4 + (1/27 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b/27 + a^5*c/9 + 2*a^4*b^2/9 - 2*a^4*b*c/9 + 10*a^4*c^2/27 + 4*a^3*b^3/9 - 29*a^3*b^2*c/27 - a^3*b*c^2 + 4*a^3*c^3/9 + 10*a^2*b^4/27 - a^2*b^3*c + 10*a^2*b^2*c^2/3 - 29*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^5/9 - 2*a*b^4*c/9 - 29*a*b^3*c^2/27 - a*b^2*c^3 - 2*a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 + 4*b^3*c^3/9 + 10*b^2*c^4/27 + b*c^5/9) := by
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
  have he : (6*a^2*b^2*c^2 + a^2*b + 3*a^2*c + 3*a*b^2 - 18*a*b*c + a*c^2 + b^2*c + 3*b*c^2) = (a^5*b/27 + a^5*c/9 + 2*a^4*b^2/9 - 2*a^4*b*c/9 + 10*a^4*c^2/27 + 4*a^3*b^3/9 - 29*a^3*b^2*c/27 - a^3*b*c^2 + 4*a^3*c^3/9 + 10*a^2*b^4/27 - a^2*b^3*c + 10*a^2*b^2*c^2/3 - 29*a^2*b*c^3/27 + 2*a^2*c^4/9 + a*b^5/9 - 2*a*b^4*c/9 - 29*a*b^3*c^2/27 - a*b^2*c^3 - 2*a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 2*b^4*c^2/9 + 4*b^3*c^3/9 + 10*b^2*c^4/27 + b*c^5/9) := by
    linear_combination (-a^4*b/27 - a^4*c/9 - 5*a^3*b^2/27 + 10*a^3*b*c/27 - a^3*b/9 - 7*a^3*c^2/27 - a^3*c/3 - 7*a^2*b^3/27 + 8*a^2*b^2*c/9 - 4*a^2*b^2/9 + 8*a^2*b*c^2/9 + 14*a^2*b*c/9 - a^2*b/3 - 5*a^2*c^3/27 - 4*a^2*c^2/9 - a^2*c - a*b^4/9 + 10*a*b^3*c/27 - a*b^3/3 + 8*a*b^2*c^2/9 + 14*a*b^2*c/9 - a*b^2 + 10*a*b*c^3/27 + 14*a*b*c^2/9 + 6*a*b*c - a*c^4/27 - a*c^3/9 - a*c^2/3 - b^4*c/27 - 5*b^3*c^2/27 - b^3*c/9 - 7*b^2*c^3/27 - 4*b^2*c^2/9 - b^2*c/3 - b*c^4/9 - b*c^3/3 - b*c^2) * hab
  have hn : 0 ≤ (6*a^2*b^2*c^2 + a^2*b + 3*a^2*c + 3*a*b^2 - 18*a*b*c + a*c^2 + b^2*c + 3*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a + 3 * b) / c + (b + 3 * c) / a + (c + 3 * a) / b ≥ 6 * (3 - a * b * c)) := @solution
#print axioms solution
