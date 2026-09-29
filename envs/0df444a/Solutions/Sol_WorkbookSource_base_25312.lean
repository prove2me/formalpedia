-- Prove2me | solution 1 for WorkbookSource.base_25312
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:03:51.632104+00:00
-- url     : https://prove2.me/submissions/266cc394-6cb6-40cd-aa5f-5b3e85053973

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 1 / b + 1 / c ≥ 3 * a / (a ^ 2 + 2 * b * c) + 3 * b / (b ^ 2 + 2 * c * a) + 3 * c / (c ^ 2 + 2 * a * b)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*b^2*c + 4*a^5*b*c^2 + 2*a^4*b^4 - 4*a^4*b^3*c - 8*a^4*b^2*c^2 - 4*a^4*b*c^3 + 2*a^4*c^4 - 4*a^3*b^4*c + 6*a^3*b^3*c^2 + 6*a^3*b^2*c^3 - 4*a^3*b*c^4 + 4*a^2*b^5*c - 8*a^2*b^4*c^2 + 6*a^2*b^3*c^3 - 8*a^2*b^2*c^4 + 4*a^2*b*c^5 + 4*a*b^5*c^2 - 4*a*b^4*c^3 - 4*a*b^3*c^4 + 4*a*b^2*c^5 + 2*b^4*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (18 : ℝ) * a^6 * (b - a)^2 + (18 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (18 : ℝ) * a^6 * (c - b)^2 + (72 : ℝ) * a^5 * (b - a)^3 + (108 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (108 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (36 : ℝ) * a^5 * (c - b)^3 + (118 : ℝ) * a^4 * (b - a)^4 + (236 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (264 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (146 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (28 : ℝ) * a^4 * (c - b)^4 + (104 : ℝ) * a^3 * (b - a)^5 + (260 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (328 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (232 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (76 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (8 : ℝ) * a^3 * (c - b)^5 + (54 : ℝ) * a^2 * (b - a)^6 + (162 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (222 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (174 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (72 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (12 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (16 : ℝ) * a^1 * (b - a)^7 + (56 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (80 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (60 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (24 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (4 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * (b - a)^8 + (8 : ℝ) * (b - a)^7 * (c - b)^1 + (12 : ℝ) * (b - a)^6 * (c - b)^2 + (8 : ℝ) * (b - a)^5 * (c - b)^3 + (2 : ℝ) * (b - a)^4 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*b^2*c + 4*a^5*b*c^2 + 2*a^4*b^4 - 4*a^4*b^3*c - 8*a^4*b^2*c^2 - 4*a^4*b*c^3 + 2*a^4*c^4 - 4*a^3*b^4*c + 6*a^3*b^3*c^2 + 6*a^3*b^2*c^3 - 4*a^3*b*c^4 + 4*a^2*b^5*c - 8*a^2*b^4*c^2 + 6*a^2*b^3*c^3 - 8*a^2*b^2*c^4 + 4*a^2*b*c^5 + 4*a*b^5*c^2 - 4*a*b^4*c^3 - 4*a*b^3*c^4 + 4*a*b^2*c^5 + 2*b^4*c^4) := by
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
  have hn : 0 ≤ (2*(a*b + a*c + b*c)*(2*a^4*b*c + a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + a^3*c^3 - 3*a^2*b^3*c + 9*a^2*b^2*c^2 - 3*a^2*b*c^3 + 2*a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 + 2*a*b*c^4 + b^3*c^3)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 1 / a + 1 / b + 1 / c ≥ 3 * a / (a ^ 2 + 2 * b * c) + 3 * b / (b ^ 2 + 2 * c * a) + 3 * c / (c ^ 2 + 2 * a * b)) := @solution
#print axioms solution
