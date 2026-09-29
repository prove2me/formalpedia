-- Prove2me | solution 1 for WorkbookSource.base_839
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:20.839034+00:00
-- url     : https://prove2.me/submissions/32421aff-145e-4bd9-8876-e1ae0059a161

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + 6 * (a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c))) ≥ 6  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6 + 3*a^5*b + 3*a^5*c - 2*a^4*b^2 - 2*a^4*c^2 - 6*a^3*b^3 - 6*a^3*c^3 - 2*a^2*b^4 + 6*a^2*b^2*c^2 - 2*a^2*c^4 + 3*a*b^5 + 3*a*c^5 + 2*b^6 + 3*b^5*c - 2*b^4*c^2 - 6*b^3*c^3 - 2*b^2*c^4 + 3*b*c^5 + 2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * a^4 * (b - a)^2 + (32 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (32 : ℝ) * a^4 * (c - b)^2 + (56 : ℝ) * a^3 * (b - a)^3 + (84 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (172 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (72 : ℝ) * a^3 * (c - b)^3 + (32 : ℝ) * a^2 * (b - a)^4 + (64 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (252 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (220 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (56 : ℝ) * a^2 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^5 + (15 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (142 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (198 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (101 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * a^1 * (c - b)^5 + (28 : ℝ) * (b - a)^4 * (c - b)^2 + (56 : ℝ) * (b - a)^3 * (c - b)^3 + (43 : ℝ) * (b - a)^2 * (c - b)^4 + (15 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6 + 3*a^5*b + 3*a^5*c - 2*a^4*b^2 - 2*a^4*c^2 - 6*a^3*b^3 - 6*a^3*c^3 - 2*a^2*b^4 + 6*a^2*b^2*c^2 - 2*a^2*c^4 + 3*a*b^5 + 3*a*c^5 + 2*b^6 + 3*b^5*c - 2*b^4*c^2 - 6*b^3*c^3 - 2*b^2*c^4 + 3*b*c^5 + 2*c^6) := by
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
  have hn : 0 ≤ (2*a^6 + 3*a^5*b + 3*a^5*c - 2*a^4*b^2 - 2*a^4*c^2 - 6*a^3*b^3 - 6*a^3*c^3 - 2*a^2*b^4 + 6*a^2*b^2*c^2 - 2*a^2*c^4 + 3*a*b^5 + 3*a*c^5 + 2*b^6 + 3*b^5*c - 2*b^4*c^2 - 6*b^3*c^3 - 2*b^2*c^4 + 3*b*c^5 + 2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a) + c / (a + b) + 6 * (a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c))) ≥ 6) := @solution
#print axioms solution
