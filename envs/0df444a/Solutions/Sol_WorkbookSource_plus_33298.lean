-- Prove2me | solution 1 for WorkbookSource.plus_33298
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:20.80559+00:00
-- url     : https://prove2.me/submissions/c73dbf06-3303-4043-97c7-8ff900340d54

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) * (1 / a + 1 / b + 1 / c) ≥ 9 * (a^2 + b^2 + c^2) / (a + b + c) + 2 * ((a - b)^2 + (b - c)^2 + (c - a)^2) / (a + b + c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b + a^4*c + a^3*b^2 - 10*a^3*b*c + a^3*c^2 + a^2*b^3 + 6*a^2*b^2*c + 6*a^2*b*c^2 + a^2*c^3 + a*b^4 - 10*a*b^3*c + 6*a*b^2*c^2 - 10*a*b*c^3 + a*c^4 + b^4*c + b^3*c^2 + b^2*c^3 + b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^3 * (b - a)^2 + (2 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^3 * (c - b)^2 + (6 : ℝ) * a^2 * (b - a)^3 + (9 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (8 : ℝ) * a^1 * (b - a)^4 + (16 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (12 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^1 * (c - b)^4 + (4 : ℝ) * (b - a)^5 + (10 : ℝ) * (b - a)^4 * (c - b)^1 + (10 : ℝ) * (b - a)^3 * (c - b)^2 + (5 : ℝ) * (b - a)^2 * (c - b)^3 + (1 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b + a^4*c + a^3*b^2 - 10*a^3*b*c + a^3*c^2 + a^2*b^3 + 6*a^2*b^2*c + 6*a^2*b*c^2 + a^2*c^3 + a*b^4 - 10*a*b^3*c + 6*a*b^2*c^2 - 10*a*b*c^3 + a*c^4 + b^4*c + b^3*c^2 + b^2*c^3 + b*c^4) := by
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
  have hn : 0 ≤ (a^4*b + a^4*c + a^3*b^2 - 10*a^3*b*c + a^3*c^2 + a^2*b^3 + 6*a^2*b^2*c + 6*a^2*b*c^2 + a^2*c^3 + a*b^4 - 10*a*b^3*c + 6*a*b^2*c^2 - 10*a*b*c^3 + a*c^4 + b^4*c + b^3*c^2 + b^2*c^3 + b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) * (1 / a + 1 / b + 1 / c) ≥ 9 * (a^2 + b^2 + c^2) / (a + b + c) + 2 * ((a - b)^2 + (b - c)^2 + (c - a)^2) / (a + b + c)) := @solution
#print axioms solution
