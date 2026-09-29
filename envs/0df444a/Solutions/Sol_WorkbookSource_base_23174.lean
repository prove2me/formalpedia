-- Prove2me | solution 1 for WorkbookSource.base_23174
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:55:10.215862+00:00
-- url     : https://prove2.me/submissions/de0fdd8b-43b8-4495-bea1-8ea914173f29

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a ^ 2 + b * c) + 1 / (b ^ 2 + c * a) + 1 / (c ^ 2 + a * b) ≥ 9 / (4 * (a * b + b * c + c * a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4*b^2 - a^4*b*c + 4*a^4*c^2 - 5*a^3*b^3 + 12*a^3*b^2*c + 12*a^3*b*c^2 - 5*a^3*c^3 + 4*a^2*b^4 + 12*a^2*b^3*c - 6*a^2*b^2*c^2 + 12*a^2*b*c^3 + 4*a^2*c^4 - a*b^4*c + 12*a*b^3*c^2 + 12*a*b^2*c^3 - a*b*c^4 + 4*b^4*c^2 - 5*b^3*c^3 + 4*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^6 + (288 : ℝ) * a^5 * (b - a)^1 + (144 : ℝ) * a^5 * (c - b)^1 + (470 : ℝ) * a^4 * (b - a)^2 + (470 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (110 : ℝ) * a^4 * (c - b)^2 + (398 : ℝ) * a^3 * (b - a)^3 + (597 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (283 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (42 : ℝ) * a^3 * (c - b)^3 + (181 : ℝ) * a^2 * (b - a)^4 + (362 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (258 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (77 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (7 : ℝ) * a^2 * (c - b)^4 + (40 : ℝ) * a^1 * (b - a)^5 + (100 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (94 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (41 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (7 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (3 : ℝ) * (b - a)^6 + (9 : ℝ) * (b - a)^5 * (c - b)^1 + (13 : ℝ) * (b - a)^4 * (c - b)^2 + (11 : ℝ) * (b - a)^3 * (c - b)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4*b^2 - a^4*b*c + 4*a^4*c^2 - 5*a^3*b^3 + 12*a^3*b^2*c + 12*a^3*b*c^2 - 5*a^3*c^3 + 4*a^2*b^4 + 12*a^2*b^3*c - 6*a^2*b^2*c^2 + 12*a^2*b*c^3 + 4*a^2*c^4 - a*b^4*c + 12*a*b^3*c^2 + 12*a*b^2*c^3 - a*b*c^4 + 4*b^4*c^2 - 5*b^3*c^3 + 4*b^2*c^4) := by
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
  have hn : 0 ≤ (4*a^4*b^2 - a^4*b*c + 4*a^4*c^2 - 5*a^3*b^3 + 12*a^3*b^2*c + 12*a^3*b*c^2 - 5*a^3*c^3 + 4*a^2*b^4 + 12*a^2*b^3*c - 6*a^2*b^2*c^2 + 12*a^2*b*c^3 + 4*a^2*c^4 - a*b^4*c + 12*a*b^3*c^2 + 12*a*b^2*c^3 - a*b*c^4 + 4*b^4*c^2 - 5*b^3*c^3 + 4*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 1 / (a ^ 2 + b * c) + 1 / (b ^ 2 + c * a) + 1 / (c ^ 2 + a * b) ≥ 9 / (4 * (a * b + b * c + c * a))) := @solution
#print axioms solution
