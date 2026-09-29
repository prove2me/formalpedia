-- Prove2me | solution 1 for WorkbookSource.base_16099
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:09.512725+00:00
-- url     : https://prove2.me/submissions/1706fb57-070b-49ea-983d-3505b3308203

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3)^2 ≥ a * b * c * (a + b + c) * (a^2 + b^2 + c^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 - a^4*b*c + 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 - a^2*b^3*c - a^2*b*c^3 - a*b^4*c - a*b^3*c^2 - a*b^2*c^3 - a*b*c^4 + b^6 + 2*b^3*c^3 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (13 : ℝ) * a^4 * (b - a)^2 + (13 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (13 : ℝ) * a^4 * (c - b)^2 + (34 : ℝ) * a^3 * (b - a)^3 + (51 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (53 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (18 : ℝ) * a^3 * (c - b)^3 + (38 : ℝ) * a^2 * (b - a)^4 + (76 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (93 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (55 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (14 : ℝ) * a^2 * (c - b)^4 + (20 : ℝ) * a^1 * (b - a)^5 + (50 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (74 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (61 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (29 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^1 * (c - b)^5 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (21 : ℝ) * (b - a)^4 * (c - b)^2 + (22 : ℝ) * (b - a)^3 * (c - b)^3 + (15 : ℝ) * (b - a)^2 * (c - b)^4 + (6 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 - a^4*b*c + 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 2*a^3*c^3 - a^2*b^3*c - a^2*b*c^3 - a*b^4*c - a*b^3*c^2 - a*b^2*c^3 - a*b*c^4 + b^6 + 2*b^3*c^3 + c^6) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3 + c^3)^2 ≥ a * b * c * (a + b + c) * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
