-- Prove2me | solution 1 for WorkbookSource.base_29201
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:08:56.585921+00:00
-- url     : https://prove2.me/submissions/adab5027-0d88-4a38-841d-43a46ead228b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 / (3 * a + b + c) + b^4 / (3 * b + c + a) + c^4 / (3 * c + a + b)) ≥ (a^3 + b^3 + c^3) / 5  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6 + 7*a^5*b + 7*a^5*c + 2*a^4*b^2 + 12*a^4*b*c + 2*a^4*c^2 - 6*a^3*b^3 - 13*a^3*b^2*c - 13*a^3*b*c^2 - 6*a^3*c^3 + 2*a^2*b^4 - 13*a^2*b^3*c - 13*a^2*b*c^3 + 2*a^2*c^4 + 7*a*b^5 + 12*a*b^4*c - 13*a*b^3*c^2 - 13*a*b^2*c^3 + 12*a*b*c^4 + 7*a*c^5 + 2*b^6 + 7*b^5*c + 2*b^4*c^2 - 6*b^3*c^3 + 2*b^2*c^4 + 7*b*c^5 + 2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (130 : ℝ) * a^4 * (b - a)^2 + (130 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (130 : ℝ) * a^4 * (c - b)^2 + (314 : ℝ) * a^3 * (b - a)^3 + (471 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (569 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (206 : ℝ) * a^3 * (c - b)^3 + (278 : ℝ) * a^2 * (b - a)^4 + (556 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (819 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (541 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (116 : ℝ) * a^2 * (c - b)^4 + (108 : ℝ) * a^1 * (b - a)^5 + (270 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (474 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (441 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (181 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (26 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^6 + (48 : ℝ) * (b - a)^5 * (c - b)^1 + (96 : ℝ) * (b - a)^4 * (c - b)^2 + (112 : ℝ) * (b - a)^3 * (c - b)^3 + (67 : ℝ) * (b - a)^2 * (c - b)^4 + (19 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6 + 7*a^5*b + 7*a^5*c + 2*a^4*b^2 + 12*a^4*b*c + 2*a^4*c^2 - 6*a^3*b^3 - 13*a^3*b^2*c - 13*a^3*b*c^2 - 6*a^3*c^3 + 2*a^2*b^4 - 13*a^2*b^3*c - 13*a^2*b*c^3 + 2*a^2*c^4 + 7*a*b^5 + 12*a*b^4*c - 13*a*b^3*c^2 - 13*a*b^2*c^3 + 12*a*b*c^4 + 7*a*c^5 + 2*b^6 + 7*b^5*c + 2*b^4*c^2 - 6*b^3*c^3 + 2*b^2*c^4 + 7*b*c^5 + 2*c^6) := by
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
  have hn : 0 ≤ (2*a^6 + 7*a^5*b + 7*a^5*c + 2*a^4*b^2 + 12*a^4*b*c + 2*a^4*c^2 - 6*a^3*b^3 - 13*a^3*b^2*c - 13*a^3*b*c^2 - 6*a^3*c^3 + 2*a^2*b^4 - 13*a^2*b^3*c - 13*a^2*b*c^3 + 2*a^2*c^4 + 7*a*b^5 + 12*a*b^4*c - 13*a*b^3*c^2 - 13*a*b^2*c^3 + 12*a*b*c^4 + 7*a*c^5 + 2*b^6 + 7*b^5*c + 2*b^4*c^2 - 6*b^3*c^3 + 2*b^2*c^4 + 7*b*c^5 + 2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^4 / (3 * a + b + c) + b^4 / (3 * b + c + a) + c^4 / (3 * c + a + b)) ≥ (a^3 + b^3 + c^3) / 5) := @solution
#print axioms solution
