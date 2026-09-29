-- Prove2me | solution 1 for WorkbookSource.base_18124
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:13:39.010693+00:00
-- url     : https://prove2.me/submissions/07fb13d7-4fa8-4b45-9813-968888505305

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 / (a + b) + 2 / (a + c) + 2 / (b + c) ≥ 5 / (a + b + 3 * c) + 5 / (a + c + 3 * b) + 5 / (b + c + 3 * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^5 + 9*a^4*b + 9*a^4*c - 15*a^3*b^2 - 15*a^3*c^2 - 15*a^2*b^3 + 6*a^2*b^2*c + 6*a^2*b*c^2 - 15*a^2*c^3 + 9*a*b^4 + 6*a*b^2*c^2 + 9*a*c^4 + 6*b^5 + 9*b^4*c - 15*b^3*c^2 - 15*b^2*c^3 + 9*b*c^4 + 6*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (60 : ℝ) * a^3 * (b - a)^2 + (60 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (60 : ℝ) * a^3 * (c - b)^2 + (78 : ℝ) * a^2 * (b - a)^3 + (117 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (243 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (102 : ℝ) * a^2 * (c - b)^3 + (24 : ℝ) * a^1 * (b - a)^4 + (48 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (222 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (198 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (48 : ℝ) * a^1 * (c - b)^4 + (54 : ℝ) * (b - a)^3 * (c - b)^2 + (81 : ℝ) * (b - a)^2 * (c - b)^3 + (39 : ℝ) * (b - a)^1 * (c - b)^4 + (6 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^5 + 9*a^4*b + 9*a^4*c - 15*a^3*b^2 - 15*a^3*c^2 - 15*a^2*b^3 + 6*a^2*b^2*c + 6*a^2*b*c^2 - 15*a^2*c^3 + 9*a*b^4 + 6*a*b^2*c^2 + 9*a*c^4 + 6*b^5 + 9*b^4*c - 15*b^3*c^2 - 15*b^2*c^3 + 9*b*c^4 + 6*c^5) := by
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
  have hn : 0 ≤ (6*a^5 + 9*a^4*b + 9*a^4*c - 15*a^3*b^2 - 15*a^3*c^2 - 15*a^2*b^3 + 6*a^2*b^2*c + 6*a^2*b*c^2 - 15*a^2*c^3 + 9*a*b^4 + 6*a*b^2*c^2 + 9*a*c^4 + 6*b^5 + 9*b^4*c - 15*b^3*c^2 - 15*b^2*c^3 + 9*b*c^4 + 6*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 2 / (a + b) + 2 / (a + c) + 2 / (b + c) ≥ 5 / (a + b + 3 * c) + 5 / (a + c + 3 * b) + 5 / (b + c + 3 * a)) := @solution
#print axioms solution
