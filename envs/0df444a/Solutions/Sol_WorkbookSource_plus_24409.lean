-- Prove2me | solution 1 for WorkbookSource.plus_24409
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:30:03.009447+00:00
-- url     : https://prove2.me/submissions/6f885613-82a8-450a-b62e-2df62cb8ba56

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^6 * b + b^6 * c + c^6 * a ≥ a * b * c * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b - a^3*b^3*c - a^3*b*c^3 - a*b^3*c^3 + a*c^6 + b^6*c) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^5 * (b - a)^2 + (9 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^5 * (c - b)^2 + (27 : ℝ) * a^4 * (b - a)^3 + (33 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (42 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (18 : ℝ) * a^4 * (c - b)^3 + (33 : ℝ) * a^3 * (b - a)^4 + (46 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (69 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (56 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (15 : ℝ) * a^3 * (c - b)^4 + (21 : ℝ) * a^2 * (b - a)^5 + (30 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (48 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (57 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (30 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^2 * (c - b)^5 + (7 : ℝ) * a^1 * (b - a)^6 + (9 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (12 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (19 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (15 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^1 * (c - b)^6 + (1 : ℝ) * (b - a)^7 + (1 : ℝ) * (b - a)^6 * (c - b)^1 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6*b - a^3*b^3*c - a^3*b*c^3 - a*b^3*c^3 + a*c^6 + b^6*c) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^5 * (c - a)^2 + (9 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (9 : ℝ) * a^5 * (b - c)^2 + (27 : ℝ) * a^4 * (c - a)^3 + (48 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (57 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (18 : ℝ) * a^4 * (b - c)^3 + (33 : ℝ) * a^3 * (c - a)^4 + (86 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (129 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (76 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (15 : ℝ) * a^3 * (b - c)^4 + (21 : ℝ) * a^2 * (c - a)^5 + (75 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (138 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (117 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (45 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (6 : ℝ) * a^2 * (b - c)^5 + (7 : ℝ) * a^1 * (c - a)^6 + (33 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (72 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (79 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (45 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (12 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (1 : ℝ) * a^1 * (b - c)^6 + (1 : ℝ) * (c - a)^7 + (6 : ℝ) * (c - a)^6 * (b - c)^1 + (15 : ℝ) * (c - a)^5 * (b - c)^2 + (20 : ℝ) * (c - a)^4 * (b - c)^3 + (15 : ℝ) * (c - a)^3 * (b - c)^4 + (6 : ℝ) * (c - a)^2 * (b - c)^5 + (1 : ℝ) * (c - a)^1 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b - a^3*b^3*c - a^3*b*c^3 - a*b^3*c^3 + a*c^6 + b^6*c) := by
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
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), a^6 * b + b^6 * c + c^6 * a ≥ a * b * c * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2)) := @solution
#print axioms solution
