-- Prove2me | solution 1 for WorkbookSource.base_3151
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:09:14.21229+00:00
-- url     : https://prove2.me/submissions/fb30fa87-bb41-47f5-af43-fedc74f53185

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ (a + b) / (a + b + 2 * c) + (b + c) / (2 * a + b + c) + (c + a) / (a + 2 * b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6 + 5*a^5*b + 5*a^5*c + a^4*b^2 + 6*a^4*b*c + a^4*c^2 - 4*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 - 4*a^3*c^3 + a^2*b^4 - 6*a^2*b^3*c - 12*a^2*b^2*c^2 - 6*a^2*b*c^3 + a^2*c^4 + 5*a*b^5 + 6*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 + 6*a*b*c^4 + 5*a*c^5 + 2*b^6 + 5*b^5*c + b^4*c^2 - 4*b^3*c^3 + b^2*c^4 + 5*b*c^5 + 2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^4 * (b - a)^2 + (96 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^4 * (c - b)^2 + (232 : ℝ) * a^3 * (b - a)^3 + (348 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (420 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (152 : ℝ) * a^3 * (c - b)^3 + (208 : ℝ) * a^2 * (b - a)^4 + (416 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (612 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (404 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (88 : ℝ) * a^2 * (c - b)^4 + (82 : ℝ) * a^1 * (b - a)^5 + (205 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (362 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (338 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (143 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (22 : ℝ) * a^1 * (c - b)^5 + (12 : ℝ) * (b - a)^6 + (36 : ℝ) * (b - a)^5 * (c - b)^1 + (75 : ℝ) * (b - a)^4 * (c - b)^2 + (90 : ℝ) * (b - a)^3 * (c - b)^3 + (56 : ℝ) * (b - a)^2 * (c - b)^4 + (17 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6 + 5*a^5*b + 5*a^5*c + a^4*b^2 + 6*a^4*b*c + a^4*c^2 - 4*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 - 4*a^3*c^3 + a^2*b^4 - 6*a^2*b^3*c - 12*a^2*b^2*c^2 - 6*a^2*b*c^3 + a^2*c^4 + 5*a*b^5 + 6*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 + 6*a*b*c^4 + 5*a*c^5 + 2*b^6 + 5*b^5*c + b^4*c^2 - 4*b^3*c^3 + b^2*c^4 + 5*b*c^5 + 2*c^6) := by
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
  have hn : 0 ≤ ((a + b + c)*(2*a^5 + 3*a^4*b + 3*a^4*c - 2*a^3*b^2 - 2*a^3*c^2 - 2*a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 - 2*a^2*c^3 + 3*a*b^4 - 4*a*b^2*c^2 + 3*a*c^4 + 2*b^5 + 3*b^4*c - 2*b^3*c^2 - 2*b^2*c^3 + 3*b*c^4 + 2*c^5)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a) + c / (a + b)) ≥ (a + b) / (a + b + 2 * c) + (b + c) / (2 * a + b + c) + (c + a) / (a + 2 * b + c)) := @solution
#print axioms solution
