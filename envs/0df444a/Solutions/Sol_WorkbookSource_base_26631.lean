-- Prove2me | solution 1 for WorkbookSource.base_26631
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:30:12.536861+00:00
-- url     : https://prove2.me/submissions/9f44c525-069e-40bf-a2c6-013da3957bd1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + (8 * (a * b + b * c + a * c) * (a + b + c)) / (9 * (a + b) * (b + c) * (c + a)) ≥ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (9*a^4*b + 9*a^4*c - a^3*b^2 - 2*a^3*b*c - a^3*c^2 - a^2*b^3 - 14*a^2*b^2*c - 14*a^2*b*c^2 - a^2*c^3 + 9*a*b^4 - 2*a*b^3*c - 14*a*b^2*c^2 - 2*a*b*c^3 + 9*a*c^4 + 9*b^4*c - b^3*c^2 - b^2*c^3 + 9*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (66 : ℝ) * a^3 * (b - a)^2 + (66 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (66 : ℝ) * a^3 * (c - b)^2 + (130 : ℝ) * a^2 * (b - a)^3 + (195 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (201 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (68 : ℝ) * a^2 * (c - b)^3 + (80 : ℝ) * a^1 * (b - a)^4 + (160 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (184 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (104 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (18 : ℝ) * a^1 * (c - b)^4 + (16 : ℝ) * (b - a)^5 + (40 : ℝ) * (b - a)^4 * (c - b)^1 + (50 : ℝ) * (b - a)^3 * (c - b)^2 + (35 : ℝ) * (b - a)^2 * (c - b)^3 + (9 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (9*a^4*b + 9*a^4*c - a^3*b^2 - 2*a^3*b*c - a^3*c^2 - a^2*b^3 - 14*a^2*b^2*c - 14*a^2*b*c^2 - a^2*c^3 + 9*a*b^4 - 2*a*b^3*c - 14*a*b^2*c^2 - 2*a*b*c^3 + 9*a*c^4 + 9*b^4*c - b^3*c^2 - b^2*c^3 + 9*b*c^4) := by
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
  have hn : 0 ≤ (9*a^4*b + 9*a^4*c - a^3*b^2 - 2*a^3*b*c - a^3*c^2 - a^2*b^3 - 14*a^2*b^2*c - 14*a^2*b*c^2 - a^2*c^3 + 9*a*b^4 - 2*a*b^3*c - 14*a*b^2*c^2 - 2*a*b*c^3 + 9*a*c^4 + 9*b^4*c - b^3*c^2 - b^2*c^3 + 9*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + (8 * (a * b + b * c + a * c) * (a + b + c)) / (9 * (a + b) * (b + c) * (c + a)) ≥ 2) := @solution
#print axioms solution
