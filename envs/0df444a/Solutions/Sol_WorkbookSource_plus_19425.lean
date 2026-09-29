-- Prove2me | solution 1 for WorkbookSource.plus_19425
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:30:01.809073+00:00
-- url     : https://prove2.me/submissions/8a5ce9a1-c001-448a-b746-7102e9f8d57f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a^7 + b^7 + c^7 + 5 * a * b * c * (a^4 + b^4 + c^4)) ≥ (a^3 + b^3 + c^3 + 3 * a * b * c) * (a^4 + b^4 + c^4 + a * b * c * (a + b + c))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7 + 6*a^5*b*c - a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 - 3*a^3*b^2*c^2 - a^3*c^4 - a^2*b^4*c - 3*a^2*b^3*c^2 - 3*a^2*b^2*c^3 - a^2*b*c^4 + 6*a*b^5*c - a*b^4*c^2 - a*b^2*c^4 + 6*a*b*c^5 + b^7 - b^4*c^3 - b^3*c^4 + c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (34 : ℝ) * a^5 * (b - a)^2 + (34 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (34 : ℝ) * a^5 * (c - b)^2 + (96 : ℝ) * a^4 * (b - a)^3 + (144 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (196 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (74 : ℝ) * a^4 * (c - b)^3 + (105 : ℝ) * a^3 * (b - a)^4 + (210 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (375 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (270 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (61 : ℝ) * a^3 * (c - b)^4 + (52 : ℝ) * a^2 * (b - a)^5 + (130 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (314 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (341 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (159 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (27 : ℝ) * a^2 * (c - b)^5 + (10 : ℝ) * a^1 * (b - a)^6 + (30 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (113 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (176 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (131 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (48 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (7 : ℝ) * a^1 * (c - b)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^2 + (30 : ℝ) * (b - a)^4 * (c - b)^3 + (34 : ℝ) * (b - a)^3 * (c - b)^4 + (21 : ℝ) * (b - a)^2 * (c - b)^5 + (7 : ℝ) * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7 + 6*a^5*b*c - a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 - 3*a^3*b^2*c^2 - a^3*c^4 - a^2*b^4*c - 3*a^2*b^3*c^2 - 3*a^2*b^2*c^3 - a^2*b*c^4 + 6*a*b^5*c - a*b^4*c^2 - a*b^2*c^4 + 6*a*b*c^5 + b^7 - b^4*c^3 - b^3*c^4 + c^7) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 2 * (a^7 + b^7 + c^7 + 5 * a * b * c * (a^4 + b^4 + c^4)) ≥ (a^3 + b^3 + c^3 + 3 * a * b * c) * (a^4 + b^4 + c^4 + a * b * c * (a + b + c))) := @solution
#print axioms solution
