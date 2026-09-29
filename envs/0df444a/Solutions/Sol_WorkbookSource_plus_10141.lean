-- Prove2me | solution 1 for WorkbookSource.plus_10141
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:04:00.049975+00:00
-- url     : https://prove2.me/submissions/6d8a21d8-237f-4279-89be-a1a250169577

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + b + 2 * c) + (b + c) / (b + c + 2 * a) + (c + a) / (c + a + 2 * b) + (2 / 3) * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≤ 13 / 6   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5 + 17*a^4*b + 17*a^4*c - a^3*b^2 + 36*a^3*b*c - a^3*c^2 - a^2*b^3 - 70*a^2*b^2*c - 70*a^2*b*c^2 - a^2*c^3 + 17*a*b^4 + 36*a*b^3*c - 70*a*b^2*c^2 + 36*a*b*c^3 + 17*a*c^4 + 2*b^5 + 17*b^4*c - b^3*c^2 - b^2*c^3 + 17*b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (184 : ℝ) * a^3 * (b - a)^2 + (184 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (184 : ℝ) * a^3 * (c - b)^2 + (362 : ℝ) * a^2 * (b - a)^3 + (543 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (561 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (190 : ℝ) * a^2 * (c - b)^3 + (216 : ℝ) * a^1 * (b - a)^4 + (432 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (494 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (278 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (44 : ℝ) * a^1 * (c - b)^4 + (36 : ℝ) * (b - a)^5 + (90 : ℝ) * (b - a)^4 * (c - b)^1 + (118 : ℝ) * (b - a)^3 * (c - b)^2 + (87 : ℝ) * (b - a)^2 * (c - b)^3 + (27 : ℝ) * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5 + 17*a^4*b + 17*a^4*c - a^3*b^2 + 36*a^3*b*c - a^3*c^2 - a^2*b^3 - 70*a^2*b^2*c - 70*a^2*b*c^2 - a^2*c^3 + 17*a*b^4 + 36*a*b^3*c - 70*a*b^2*c^2 + 36*a*b*c^3 + 17*a*c^4 + 2*b^5 + 17*b^4*c - b^3*c^2 - b^2*c^3 + 17*b*c^4 + 2*c^5) := by
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
  have hn : 0 ≤ (2*a^5 + 17*a^4*b + 17*a^4*c - a^3*b^2 + 36*a^3*b*c - a^3*c^2 - a^2*b^3 - 70*a^2*b^2*c - 70*a^2*b*c^2 - a^2*c^3 + 17*a*b^4 + 36*a*b^3*c - 70*a*b^2*c^2 + 36*a*b*c^3 + 17*a*c^4 + 2*b^5 + 17*b^4*c - b^3*c^2 - b^2*c^3 + 17*b*c^4 + 2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (a + b + 2 * c) + (b + c) / (b + c + 2 * a) + (c + a) / (c + a + 2 * b) + (2 / 3) * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≤ 13 / 6) := @solution
#print axioms solution
