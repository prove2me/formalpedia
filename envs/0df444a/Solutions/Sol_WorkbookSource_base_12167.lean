-- Prove2me | solution 1 for WorkbookSource.base_12167
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:42:11.249177+00:00
-- url     : https://prove2.me/submissions/56c9353e-b908-4368-97c8-88e002484625

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) ≥ 9 / (2 * (a * b + b * c + c * a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 - a^2*b^3*c - a^2*b*c^3 - a*b^3*c^2 - a*b^2*c^3 + 2*b^3*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^4 * (b - a)^2 + (4 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^4 * (c - b)^2 + (14 : ℝ) * a^3 * (b - a)^3 + (21 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (11 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (2 : ℝ) * a^3 * (c - b)^3 + (18 : ℝ) * a^2 * (b - a)^4 + (36 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (21 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (10 : ℝ) * a^1 * (b - a)^5 + (25 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (20 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (5 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2 : ℝ) * (b - a)^6 + (6 : ℝ) * (b - a)^5 * (c - b)^1 + (6 : ℝ) * (b - a)^4 * (c - b)^2 + (2 : ℝ) * (b - a)^3 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 - a^2*b^3*c - a^2*b*c^3 - a*b^3*c^2 - a*b^2*c^3 + 2*b^3*c^3) := by
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
  have hn : 0 ≤ (2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 - a^2*b^3*c - a^2*b*c^3 - a*b^3*c^2 - a*b^2*c^3 + 2*b^3*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 1 / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) ≥ 9 / (2 * (a * b + b * c + c * a))) := @solution
#print axioms solution
