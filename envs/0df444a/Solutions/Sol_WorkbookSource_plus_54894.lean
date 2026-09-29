-- Prove2me | solution 1 for WorkbookSource.plus_54894
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:52.512149+00:00
-- url     : https://prove2.me/submissions/8d022be0-9245-4eca-b86a-02b813c4d853

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 * (b + c - a) / (a^2 + b * c) + b^3 * (c + a - b) / (b^2 + c * a) + c^3 * (a + b - c) / (c^2 + a * b)) ≤ (a * b + b * c + c * a) / 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6*b*c + 2*a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + 2*a^5*c^3 - 3*a^4*b^4 - a^4*b^3*c + 3*a^4*b^2*c^2 - a^4*b*c^3 - 3*a^4*c^4 + 2*a^3*b^5 - a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 + 2*a^3*c^5 - a^2*b^5*c + 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 3*a^2*b^2*c^4 - a^2*b*c^5 + 2*a*b^6*c - a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 - a*b^2*c^5 + 2*a*b*c^6 + 2*b^5*c^3 - 3*b^4*c^4 + 2*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^6 * (b - a)^2 + (16 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^6 * (c - b)^2 + (58 : ℝ) * a^5 * (b - a)^3 + (87 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (105 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (38 : ℝ) * a^5 * (c - b)^3 + (85 : ℝ) * a^4 * (b - a)^4 + (170 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (250 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (165 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (35 : ℝ) * a^4 * (c - b)^4 + (66 : ℝ) * a^3 * (b - a)^5 + (165 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (286 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (264 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (105 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (14 : ℝ) * a^3 * (c - b)^5 + (30 : ℝ) * a^2 * (b - a)^6 + (90 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (175 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (200 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (112 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (27 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^2 * (c - b)^6 + (8 : ℝ) * a^1 * (b - a)^7 + (28 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (58 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (75 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (52 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (17 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (b - a)^8 + (4 : ℝ) * (b - a)^7 * (c - b)^1 + (8 : ℝ) * (b - a)^6 * (c - b)^2 + (10 : ℝ) * (b - a)^5 * (c - b)^3 + (7 : ℝ) * (b - a)^4 * (c - b)^4 + (2 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6*b*c + 2*a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + 2*a^5*c^3 - 3*a^4*b^4 - a^4*b^3*c + 3*a^4*b^2*c^2 - a^4*b*c^3 - 3*a^4*c^4 + 2*a^3*b^5 - a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 + 2*a^3*c^5 - a^2*b^5*c + 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 3*a^2*b^2*c^4 - a^2*b*c^5 + 2*a*b^6*c - a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 - a*b^2*c^5 + 2*a*b*c^6 + 2*b^5*c^3 - 3*b^4*c^4 + 2*b^3*c^5) := by
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
  have hn : 0 ≤ (2*a^6*b*c + 2*a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + 2*a^5*c^3 - 3*a^4*b^4 - a^4*b^3*c + 3*a^4*b^2*c^2 - a^4*b*c^3 - 3*a^4*c^4 + 2*a^3*b^5 - a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 + 2*a^3*c^5 - a^2*b^5*c + 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 3*a^2*b^2*c^4 - a^2*b*c^5 + 2*a*b^6*c - a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 - a*b^2*c^5 + 2*a*b*c^6 + 2*b^5*c^3 - 3*b^4*c^4 + 2*b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 * (b + c - a) / (a^2 + b * c) + b^3 * (c + a - b) / (b^2 + c * a) + c^3 * (a + b - c) / (c^2 + a * b)) ≤ (a * b + b * c + c * a) / 2) := @solution
#print axioms solution
