-- Prove2me | solution 1 for WorkbookSource.base_42967
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:38:44.43141+00:00
-- url     : https://prove2.me/submissions/077a56fa-5d7f-400a-9bc2-ad8d17c331a7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 - b * c) / (b + c) + (1 - c * a) / (c + a) + (1 - a * b) / (a + b) ≥ (9 - (a + b + c) ^ 2) / (2 * (a + b + c))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b + a^4*c + a^3*b^2 + a^3*c^2 + 2*a^3 + a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 - a^2*b + a^2*c^3 - a^2*c + a*b^4 - 4*a*b^2*c^2 - a*b^2 + a*c^4 - a*c^2 + b^4*c + b^3*c^2 + 2*b^3 + b^2*c^3 - b^2*c + b*c^4 - b*c^2 + 2*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^3 * (b - a)^2 + (12 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^3 * (c - b)^2 + (26 : ℝ) * a^2 * (b - a)^3 + (39 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (33 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (10 : ℝ) * a^2 * (c - b)^3 + (18 : ℝ) * a^1 * (b - a)^4 + (36 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (32 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (4 : ℝ) * a^1 * (b - a)^2 + (14 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^2 + (4 : ℝ) * (b - a)^5 + (10 : ℝ) * (b - a)^4 * (c - b)^1 + (10 : ℝ) * (b - a)^3 * (c - b)^2 + (2 : ℝ) * (b - a)^3 + (5 : ℝ) * (b - a)^2 * (c - b)^3 + (3 : ℝ) * (b - a)^2 * (c - b)^1 + (1 : ℝ) * (b - a)^1 * (c - b)^4 + (5 : ℝ) * (b - a)^1 * (c - b)^2 + (2 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b + a^4*c + a^3*b^2 + a^3*c^2 + 2*a^3 + a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 - a^2*b + a^2*c^3 - a^2*c + a*b^4 - 4*a*b^2*c^2 - a*b^2 + a*c^4 - a*c^2 + b^4*c + b^3*c^2 + 2*b^3 + b^2*c^3 - b^2*c + b*c^4 - b*c^2 + 2*c^3) := by
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
  have hn : 0 ≤ (a^4*b + a^4*c + a^3*b^2 + a^3*c^2 + 2*a^3 + a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 - a^2*b + a^2*c^3 - a^2*c + a*b^4 - 4*a*b^2*c^2 - a*b^2 + a*c^4 - a*c^2 + b^4*c + b^3*c^2 + 2*b^3 + b^2*c^3 - b^2*c + b*c^4 - b*c^2 + 2*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 - b * c) / (b + c) + (1 - c * a) / (c + a) + (1 - a * b) / (a + b) ≥ (9 - (a + b + c) ^ 2) / (2 * (a + b + c))) := @solution
#print axioms solution
