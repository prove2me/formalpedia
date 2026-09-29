-- Prove2me | solution 1 for WorkbookSource.base_39698
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:47:27.658562+00:00
-- url     : https://prove2.me/submissions/62928d7b-b95d-42be-867a-12c795b49f6d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a)^2 ≥ 3 * (a^3 / b + b^3 / c + c^3 / a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*c^2 - 3*a^5*b*c^2 + 2*a^4*b^3*c + 2*a^3*b*c^4 + a^2*b^6 - 3*a^2*b^5*c + 2*a*b^4*c^3 - 3*a*b^2*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * a^6 * (b - a)^2 + (1 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (1 : ℝ) * a^6 * (c - b)^2 + (6 : ℝ) * a^5 * (b - a)^3 + (9 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (3 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (17 : ℝ) * a^4 * (b - a)^4 + (34 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (21 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (4 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^4 * (c - b)^4 + (25 : ℝ) * a^3 * (b - a)^5 + (68 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (72 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (40 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (17 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (3 : ℝ) * a^3 * (c - b)^5 + (19 : ℝ) * a^2 * (b - a)^6 + (69 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (105 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (88 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (45 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (12 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^2 * (c - b)^6 + (7 : ℝ) * a^1 * (b - a)^7 + (33 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (66 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (72 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (45 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (15 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (b - a)^8 + (6 : ℝ) * (b - a)^7 * (c - b)^1 + (15 : ℝ) * (b - a)^6 * (c - b)^2 + (20 : ℝ) * (b - a)^5 * (c - b)^3 + (15 : ℝ) * (b - a)^4 * (c - b)^4 + (6 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6*c^2 - 3*a^5*b*c^2 + 2*a^4*b^3*c + 2*a^3*b*c^4 + a^2*b^6 - 3*a^2*b^5*c + 2*a*b^4*c^3 - 3*a*b^2*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * a^6 * (c - a)^2 + (1 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (1 : ℝ) * a^6 * (b - c)^2 + (6 : ℝ) * a^5 * (c - a)^3 + (9 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (3 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (17 : ℝ) * a^4 * (c - a)^4 + (34 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (21 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (4 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (2 : ℝ) * a^4 * (b - c)^4 + (25 : ℝ) * a^3 * (c - a)^5 + (57 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (50 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (18 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (6 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (3 : ℝ) * a^3 * (b - c)^5 + (19 : ℝ) * a^2 * (c - a)^6 + (45 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (45 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (22 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (6 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (3 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (1 : ℝ) * a^2 * (b - c)^6 + (7 : ℝ) * a^1 * (c - a)^7 + (16 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (15 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (8 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (2 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (1 : ℝ) * (c - a)^8 + (2 : ℝ) * (c - a)^7 * (b - c)^1 + (1 : ℝ) * (c - a)^6 * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*c^2 - 3*a^5*b*c^2 + 2*a^4*b^3*c + 2*a^3*b*c^4 + a^2*b^6 - 3*a^2*b^5*c + 2*a*b^4*c^3 - 3*a*b^2*c^5 + b^2*c^6) := by
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
  have hn : 0 ≤ (a^6*c^2 - 3*a^5*b*c^2 + 2*a^4*b^3*c + 2*a^3*b*c^4 + a^2*b^6 - 3*a^2*b^5*c + 2*a*b^4*c^3 - 3*a*b^2*c^5 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / b + b^2 / c + c^2 / a)^2 ≥ 3 * (a^3 / b + b^3 / c + c^3 / a)) := @solution
#print axioms solution
