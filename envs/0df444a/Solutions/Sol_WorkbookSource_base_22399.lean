-- Prove2me | solution 1 for WorkbookSource.base_22399
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:53:15.818805+00:00
-- url     : https://prove2.me/submissions/f8186010-9a00-4bd5-a7f2-ac66c3189ed3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (3 * a * b * c) ≥ (2 - (a * b + b * c + c * a) / (a^2 + b^2 + c^2))^2 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b + a^6*c - 11*a^5*b*c + a^4*b^3 + 13*a^4*b^2*c + 13*a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 25*a^3*b^3*c + 6*a^3*b^2*c^2 - 25*a^3*b*c^3 + a^3*c^4 + 13*a^2*b^4*c + 6*a^2*b^3*c^2 + 6*a^2*b^2*c^3 + 13*a^2*b*c^4 + a*b^6 - 11*a*b^5*c + 13*a*b^4*c^2 - 25*a*b^3*c^3 + 13*a*b^2*c^4 - 11*a*b*c^5 + a*c^6 + b^6*c + b^4*c^3 + b^3*c^4 + b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^3 * (b - a)^4 + (6 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (9 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (6 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (3 : ℝ) * a^3 * (c - b)^4 + (8 : ℝ) * a^2 * (b - a)^5 + (20 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (26 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (19 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (7 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (1 : ℝ) * a^2 * (c - b)^5 + (9 : ℝ) * a^1 * (b - a)^6 + (27 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (41 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (37 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (21 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (7 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^1 * (c - b)^6 + (4 : ℝ) * (b - a)^7 + (14 : ℝ) * (b - a)^6 * (c - b)^1 + (24 : ℝ) * (b - a)^5 * (c - b)^2 + (25 : ℝ) * (b - a)^4 * (c - b)^3 + (16 : ℝ) * (b - a)^3 * (c - b)^4 + (6 : ℝ) * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b + a^6*c - 11*a^5*b*c + a^4*b^3 + 13*a^4*b^2*c + 13*a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 25*a^3*b^3*c + 6*a^3*b^2*c^2 - 25*a^3*b*c^3 + a^3*c^4 + 13*a^2*b^4*c + 6*a^2*b^3*c^2 + 6*a^2*b^2*c^3 + 13*a^2*b*c^4 + a*b^6 - 11*a*b^5*c + 13*a*b^4*c^2 - 25*a*b^3*c^3 + 13*a*b^2*c^4 - 11*a*b*c^5 + a*c^6 + b^6*c + b^4*c^3 + b^3*c^4 + b*c^6) := by
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
  have hn : 0 ≤ ((a^2 - a*b - a*c + b^2 - b*c + c^2)*(a^4*b + a^4*c + a^3*b^2 - 9*a^3*b*c + a^3*c^2 + a^2*b^3 + 5*a^2*b^2*c + 5*a^2*b*c^2 + a^2*c^3 + a*b^4 - 9*a*b^3*c + 5*a*b^2*c^2 - 9*a*b*c^3 + a*c^4 + b^4*c + b^3*c^2 + b^2*c^3 + b*c^4)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3 + c^3) / (3 * a * b * c) ≥ (2 - (a * b + b * c + c * a) / (a^2 + b^2 + c^2))^2 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a)) := @solution
#print axioms solution
