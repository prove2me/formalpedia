-- Prove2me | solution 1 for WorkbookSource.base_16854
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:06:23.380702+00:00
-- url     : https://prove2.me/submissions/47eb5170-3f91-489d-acec-b64c70350e09

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2 + 4 * (a ^ 4 + b ^ 4 + c ^ 4 - a * b * c * (a + b + c)) / (a + b + c) ^ 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^7 - a^6*b - a^6*c - a^5*b^2 - a^5*c^2 + a^4*b^2*c + a^4*b*c^2 - a^2*b^5 + a^2*b^4*c + a^2*b*c^4 - a^2*c^5 - a*b^6 + a*b^4*c^2 + a*b^2*c^4 - a*c^6 + 2*b^7 - b^6*c - b^5*c^2 - b^2*c^5 - b*c^6 + 2*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^5 * (b - a)^2 + (4 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^5 * (c - b)^2 + (2 : ℝ) * a^4 * (b - a)^3 + (3 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (37 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (18 : ℝ) * a^4 * (c - b)^3 + (100 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (100 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (32 : ℝ) * a^3 * (c - b)^4 + (124 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (186 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (118 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (28 : ℝ) * a^2 * (c - b)^5 + (72 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (144 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (136 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (64 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (12 : ℝ) * a^1 * (c - b)^6 + (16 : ℝ) * (b - a)^5 * (c - b)^2 + (40 : ℝ) * (b - a)^4 * (c - b)^3 + (50 : ℝ) * (b - a)^3 * (c - b)^4 + (35 : ℝ) * (b - a)^2 * (c - b)^5 + (13 : ℝ) * (b - a)^1 * (c - b)^6 + (2 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^7 - a^6*b - a^6*c - a^5*b^2 - a^5*c^2 + a^4*b^2*c + a^4*b*c^2 - a^2*b^5 + a^2*b^4*c + a^2*b*c^4 - a^2*c^5 - a*b^6 + a*b^4*c^2 + a*b^2*c^4 - a*c^6 + 2*b^7 - b^6*c - b^5*c^2 - b^2*c^5 - b*c^6 + 2*c^7) := by
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
  have hn : 0 ≤ (2*a^7 - a^6*b - a^6*c - a^5*b^2 - a^5*c^2 + a^4*b^2*c + a^4*b*c^2 - a^2*b^5 + a^2*b^4*c + a^2*b*c^4 - a^2*c^5 - a*b^6 + a*b^4*c^2 + a*b^2*c^4 - a*c^6 + 2*b^7 - b^6*c - b^5*c^2 - b^2*c^5 - b*c^6 + 2*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2 + 4 * (a ^ 4 + b ^ 4 + c ^ 4 - a * b * c * (a + b + c)) / (a + b + c) ^ 4) := @solution
#print axioms solution
