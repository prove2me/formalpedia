-- Prove2me | solution 1 for WorkbookSource.base_43680
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:12.58026+00:00
-- url     : https://prove2.me/submissions/7bc4fe9d-4959-401e-82ad-541d3184fe34

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b * (b + 2 * c)) + b / (c * (c + 2 * a)) + c / (a * (a + 2 * b))) ≥ 3 / (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*c + 6*a^4*b*c + 3*a^4*c^2 + a^3*b^3 - 5*a^3*b*c^2 + a^3*c^3 + 3*a^2*b^4 - 5*a^2*b^3*c - 21*a^2*b^2*c^2 + 2*a*b^5 + 6*a*b^4*c - 5*a*b^2*c^3 + 6*a*b*c^4 + b^3*c^3 + 3*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (42 : ℝ) * a^4 * (b - a)^2 + (42 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (42 : ℝ) * a^4 * (c - b)^2 + (115 : ℝ) * a^3 * (b - a)^3 + (192 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (183 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (53 : ℝ) * a^3 * (c - b)^3 + (112 : ℝ) * a^2 * (b - a)^4 + (263 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (288 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (137 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (19 : ℝ) * a^2 * (c - b)^4 + (45 : ℝ) * a^1 * (b - a)^5 + (140 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (185 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (118 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (32 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (6 : ℝ) * (b - a)^6 + (25 : ℝ) * (b - a)^5 * (c - b)^1 + (41 : ℝ) * (b - a)^4 * (c - b)^2 + (33 : ℝ) * (b - a)^3 * (c - b)^3 + (13 : ℝ) * (b - a)^2 * (c - b)^4 + (2 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*c + 6*a^4*b*c + 3*a^4*c^2 + a^3*b^3 - 5*a^3*b*c^2 + a^3*c^3 + 3*a^2*b^4 - 5*a^2*b^3*c - 21*a^2*b^2*c^2 + 2*a*b^5 + 6*a*b^4*c - 5*a*b^2*c^3 + 6*a*b*c^4 + b^3*c^3 + 3*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (42 : ℝ) * a^4 * (c - a)^2 + (42 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (42 : ℝ) * a^4 * (b - c)^2 + (115 : ℝ) * a^3 * (c - a)^3 + (153 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (144 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (53 : ℝ) * a^3 * (b - c)^3 + (112 : ℝ) * a^2 * (c - a)^4 + (185 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (171 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (98 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (19 : ℝ) * a^2 * (b - c)^4 + (45 : ℝ) * a^1 * (c - a)^5 + (85 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (75 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (47 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (16 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^1 * (b - c)^5 + (6 : ℝ) * (c - a)^6 + (11 : ℝ) * (c - a)^5 * (b - c)^1 + (6 : ℝ) * (c - a)^4 * (b - c)^2 + (1 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*c + 6*a^4*b*c + 3*a^4*c^2 + a^3*b^3 - 5*a^3*b*c^2 + a^3*c^3 + 3*a^2*b^4 - 5*a^2*b^3*c - 21*a^2*b^2*c^2 + 2*a*b^5 + 6*a*b^4*c - 5*a*b^2*c^3 + 6*a*b*c^4 + b^3*c^3 + 3*b^2*c^4 + 2*b*c^5) := by
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
  have hn : 0 ≤ (2*a^5*c + 6*a^4*b*c + 3*a^4*c^2 + a^3*b^3 - 5*a^3*b*c^2 + a^3*c^3 + 3*a^2*b^4 - 5*a^2*b^3*c - 21*a^2*b^2*c^2 + 2*a*b^5 + 6*a*b^4*c - 5*a*b^2*c^3 + 6*a*b*c^4 + b^3*c^3 + 3*b^2*c^4 + 2*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b * (b + 2 * c)) + b / (c * (c + 2 * a)) + c / (a * (a + 2 * b))) ≥ 3 / (a + b + c)) := @solution
#print axioms solution
