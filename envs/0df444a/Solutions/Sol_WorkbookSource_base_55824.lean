-- Prove2me | solution 1 for WorkbookSource.base_55824
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:31.556825+00:00
-- url     : https://prove2.me/submissions/dff3f02b-aeeb-438a-9c75-fbdaa96c0521

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 * c^3 + b^4 * a^3 + c^4 * b^3 + 2 * a * b * c * (a^4 + b^4 + c^4) ≥ 3 * a * b * c * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b*c + a^4*c^3 + a^3*b^4 - 3*a^3*b^3*c - 3*a^3*b*c^3 + 2*a*b^5*c - 3*a*b^3*c^3 + 2*a*b*c^5 + b^3*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (11 : ℝ) * a^5 * (b - a)^2 + (11 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (11 : ℝ) * a^5 * (c - b)^2 + (36 : ℝ) * a^4 * (b - a)^3 + (57 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (59 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (19 : ℝ) * a^4 * (c - b)^3 + (45 : ℝ) * a^3 * (b - a)^4 + (98 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (117 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (64 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (11 : ℝ) * a^3 * (c - b)^4 + (27 : ℝ) * a^2 * (b - a)^5 + (75 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (104 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (75 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (23 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^2 * (c - b)^5 + (8 : ℝ) * a^1 * (b - a)^6 + (27 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (41 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (33 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (13 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (b - a)^7 + (4 : ℝ) * (b - a)^6 * (c - b)^1 + (6 : ℝ) * (b - a)^5 * (c - b)^2 + (4 : ℝ) * (b - a)^4 * (c - b)^3 + (1 : ℝ) * (b - a)^3 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*b*c + a^4*c^3 + a^3*b^4 - 3*a^3*b^3*c - 3*a^3*b*c^3 + 2*a*b^5*c - 3*a*b^3*c^3 + 2*a*b*c^5 + b^3*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (11 : ℝ) * a^5 * (c - a)^2 + (11 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (11 : ℝ) * a^5 * (b - c)^2 + (36 : ℝ) * a^4 * (c - a)^3 + (51 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (53 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (19 : ℝ) * a^4 * (b - c)^3 + (45 : ℝ) * a^3 * (c - a)^4 + (82 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (93 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (56 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (11 : ℝ) * a^3 * (b - c)^4 + (27 : ℝ) * a^2 * (c - a)^5 + (60 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (74 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (57 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (20 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^2 * (b - c)^5 + (8 : ℝ) * a^1 * (c - a)^6 + (21 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (26 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (21 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (10 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (1 : ℝ) * (c - a)^7 + (3 : ℝ) * (c - a)^6 * (b - c)^1 + (3 : ℝ) * (c - a)^5 * (b - c)^2 + (1 : ℝ) * (c - a)^4 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b*c + a^4*c^3 + a^3*b^4 - 3*a^3*b^3*c - 3*a^3*b*c^3 + 2*a*b^5*c - 3*a*b^3*c^3 + 2*a*b*c^5 + b^3*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^4 * c^3 + b^4 * a^3 + c^4 * b^3 + 2 * a * b * c * (a^4 + b^4 + c^4) ≥ 3 * a * b * c * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) := @solution
#print axioms solution
