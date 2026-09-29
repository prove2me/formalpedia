-- Prove2me | solution 1 for WorkbookSource.base_32906
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:47:22.85457+00:00
-- url     : https://prove2.me/submissions/07484bd3-a8f5-485d-9e25-64458176ff37

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + 3 * (a * b + b * c + c * a) / (a + b + c) ^ 2) ≥ 5 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5 + a^4*b + a^4*c - a^3*b^2 - a^3*c^2 - a^2*b^3 - 2*a^2*b^2*c - 2*a^2*b*c^2 - a^2*c^3 + a*b^4 - 2*a*b^2*c^2 + a*c^4 + 2*b^5 + b^4*c - b^3*c^2 - b^2*c^3 + b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^3 * (b - a)^2 + (20 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (20 : ℝ) * a^3 * (c - b)^2 + (34 : ℝ) * a^2 * (b - a)^3 + (51 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (69 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (26 : ℝ) * a^2 * (c - b)^3 + (20 : ℝ) * a^1 * (b - a)^4 + (40 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (70 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (50 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (12 : ℝ) * a^1 * (c - b)^4 + (4 : ℝ) * (b - a)^5 + (10 : ℝ) * (b - a)^4 * (c - b)^1 + (22 : ℝ) * (b - a)^3 * (c - b)^2 + (23 : ℝ) * (b - a)^2 * (c - b)^3 + (11 : ℝ) * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5 + a^4*b + a^4*c - a^3*b^2 - a^3*c^2 - a^2*b^3 - 2*a^2*b^2*c - 2*a^2*b*c^2 - a^2*c^3 + a*b^4 - 2*a*b^2*c^2 + a*c^4 + 2*b^5 + b^4*c - b^3*c^2 - b^2*c^3 + b*c^4 + 2*c^5) := by
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
  have hn : 0 ≤ (2*a^5 + a^4*b + a^4*c - a^3*b^2 - a^3*c^2 - a^2*b^3 - 2*a^2*b^2*c - 2*a^2*b*c^2 - a^2*c^3 + a*b^4 - 2*a*b^2*c^2 + a*c^4 + 2*b^5 + b^4*c - b^3*c^2 - b^2*c^3 + b*c^4 + 2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a) + c / (a + b) + 3 * (a * b + b * c + c * a) / (a + b + c) ^ 2) ≥ 5 / 2) := @solution
#print axioms solution
