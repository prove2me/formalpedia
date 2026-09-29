-- Prove2me | solution 1 for WorkbookSource.base_38511
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:39:49.030977+00:00
-- url     : https://prove2.me/submissions/d4318010-b978-41da-894b-36f7476f89aa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / c ^ 2 + (c + a) / b ^ 2 + (b + c) / a ^ 2 ≥ 9 / (a + b + c) + 1 / a + 1 / b + 1 / c  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2 + a^4*c^2 + 2*a^3*b^3 + 2*a^3*c^3 + a^2*b^4 - 12*a^2*b^2*c^2 + a^2*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (14 : ℝ) * a^4 * (b - a)^2 + (14 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (14 : ℝ) * a^4 * (c - b)^2 + (44 : ℝ) * a^3 * (b - a)^3 + (66 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (46 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^3 * (c - b)^3 + (50 : ℝ) * a^2 * (b - a)^4 + (100 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (72 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (22 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^2 * (c - b)^4 + (24 : ℝ) * a^1 * (b - a)^5 + (60 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (52 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (18 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (13 : ℝ) * (b - a)^4 * (c - b)^2 + (6 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2 + a^4*c^2 + 2*a^3*b^3 + 2*a^3*c^3 + a^2*b^4 - 12*a^2*b^2*c^2 + a^2*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
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
  have hn : 0 ≤ (a^4*b^2 + a^4*c^2 + 2*a^3*b^3 + 2*a^3*c^3 + a^2*b^4 - 12*a^2*b^2*c^2 + a^2*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / c ^ 2 + (c + a) / b ^ 2 + (b + c) / a ^ 2 ≥ 9 / (a + b + c) + 1 / a + 1 / b + 1 / c) := @solution
#print axioms solution
