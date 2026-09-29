-- Prove2me | solution 1 for WorkbookSource.base_33608
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:30:15.952352+00:00
-- url     : https://prove2.me/submissions/722c6891-4f5d-41c2-bd93-7c8c4fd7ad55

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + 3 * a * b * c) / (b + c) + (b^3 + 3 * a * b * c) / (c + a) + (c^3 + 3 * a * b * c) / (a + b) ≥ 2 * (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5 + a^4*b + a^4*c - 2*a^3*b^2 - 2*a^3*c^2 - 2*a^2*b^3 + a^2*b^2*c + a^2*b*c^2 - 2*a^2*c^3 + a*b^4 + a*b^2*c^2 + a*c^4 + b^5 + b^4*c - 2*b^3*c^2 - 2*b^2*c^3 + b*c^4 + c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^3 * (b - a)^2 + (8 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^3 * (c - b)^2 + (10 : ℝ) * a^2 * (b - a)^3 + (15 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (33 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (14 : ℝ) * a^2 * (c - b)^3 + (3 : ℝ) * a^1 * (b - a)^4 + (6 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (31 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (28 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (7 : ℝ) * a^1 * (c - b)^4 + (8 : ℝ) * (b - a)^3 * (c - b)^2 + (12 : ℝ) * (b - a)^2 * (c - b)^3 + (6 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5 + a^4*b + a^4*c - 2*a^3*b^2 - 2*a^3*c^2 - 2*a^2*b^3 + a^2*b^2*c + a^2*b*c^2 - 2*a^2*c^3 + a*b^4 + a*b^2*c^2 + a*c^4 + b^5 + b^4*c - 2*b^3*c^2 - 2*b^2*c^3 + b*c^4 + c^5) := by
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
  have hn : 0 ≤ (a^5 + a^4*b + a^4*c - 2*a^3*b^2 - 2*a^3*c^2 - 2*a^2*b^3 + a^2*b^2*c + a^2*b*c^2 - 2*a^2*c^3 + a*b^4 + a*b^2*c^2 + a*c^4 + b^5 + b^4*c - 2*b^3*c^2 - 2*b^2*c^3 + b*c^4 + c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + 3 * a * b * c) / (b + c) + (b^3 + 3 * a * b * c) / (c + a) + (c^3 + 3 * a * b * c) / (a + b) ≥ 2 * (a * b + b * c + c * a)) := @solution
#print axioms solution
