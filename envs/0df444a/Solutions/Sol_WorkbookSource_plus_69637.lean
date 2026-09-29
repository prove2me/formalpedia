-- Prove2me | solution 1 for WorkbookSource.plus_69637
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:51:25.752705+00:00
-- url     : https://prove2.me/submissions/303ac6aa-a5d9-4301-a139-209577545cc7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + (9 * (a * b + b * c + c * a)) / (2 * (a + b + c) ^ 2)) ≥ 3   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5 - a^3*b^2 - a^3*c^2 - a^2*b^3 - a^2*c^3 + 2*b^5 - b^3*c^2 - b^2*c^3 + 2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^3 * (b - a)^2 + (12 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^3 * (c - b)^2 + (18 : ℝ) * a^2 * (b - a)^3 + (27 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (45 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (18 : ℝ) * a^2 * (c - b)^3 + (10 : ℝ) * a^1 * (b - a)^4 + (20 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (48 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (38 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (10 : ℝ) * a^1 * (c - b)^4 + (2 : ℝ) * (b - a)^5 + (5 : ℝ) * (b - a)^4 * (c - b)^1 + (16 : ℝ) * (b - a)^3 * (c - b)^2 + (19 : ℝ) * (b - a)^2 * (c - b)^3 + (10 : ℝ) * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5 - a^3*b^2 - a^3*c^2 - a^2*b^3 - a^2*c^3 + 2*b^5 - b^3*c^2 - b^2*c^3 + 2*c^5) := by
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
  have hn : 0 ≤ (2*a^5 - a^3*b^2 - a^3*c^2 - a^2*b^3 - a^2*c^3 + 2*b^5 - b^3*c^2 - b^2*c^3 + 2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a) + c / (a + b) + (9 * (a * b + b * c + c * a)) / (2 * (a + b + c) ^ 2)) ≥ 3) := @solution
#print axioms solution
