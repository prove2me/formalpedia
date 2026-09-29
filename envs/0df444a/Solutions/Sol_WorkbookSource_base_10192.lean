-- Prove2me | solution 1 for WorkbookSource.base_10192
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:18.990319+00:00
-- url     : https://prove2.me/submissions/453ba9d2-dfd9-4082-896e-9afeb84ce7b8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 + 1) * (b^4 + 1) * (c^4 + 1) ≥ (a^3 * b + 1) * (b^3 * c + 1) * (c^3 * a + 1)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^4 - a^4*b*c^3 + a^4*c^4 + a^4 - a^3*b^4*c - a^3*b - a*b^3*c^4 - a*c^3 + b^4*c^4 + b^4 - b^3*c + c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^6 * (b - a)^2 + (3 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^6 * (c - b)^2 + (15 : ℝ) * a^5 * (b - a)^3 + (21 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (12 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^5 * (c - b)^3 + (31 : ℝ) * a^4 * (b - a)^4 + (57 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (33 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (7 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^4 * (c - b)^4 + (34 : ℝ) * a^3 * (b - a)^5 + (79 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (60 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (16 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (1 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (21 : ℝ) * a^2 * (b - a)^6 + (60 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (60 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (24 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (3 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (3 : ℝ) * a^2 * (b - a)^2 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^2 * (c - b)^2 + (7 : ℝ) * a^1 * (b - a)^7 + (24 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (30 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (16 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (3 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (3 : ℝ) * a^1 * (b - a)^3 + (6 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (9 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^1 * (c - b)^3 + (1 : ℝ) * (b - a)^8 + (4 : ℝ) * (b - a)^7 * (c - b)^1 + (6 : ℝ) * (b - a)^6 * (c - b)^2 + (4 : ℝ) * (b - a)^5 * (c - b)^3 + (1 : ℝ) * (b - a)^4 * (c - b)^4 + (1 : ℝ) * (b - a)^4 + (3 : ℝ) * (b - a)^3 * (c - b)^1 + (6 : ℝ) * (b - a)^2 * (c - b)^2 + (4 : ℝ) * (b - a)^1 * (c - b)^3 + (1 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b^4 - a^4*b*c^3 + a^4*c^4 + a^4 - a^3*b^4*c - a^3*b - a*b^3*c^4 - a*c^3 + b^4*c^4 + b^4 - b^3*c + c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^6 * (c - a)^2 + (3 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (3 : ℝ) * a^6 * (b - c)^2 + (15 : ℝ) * a^5 * (c - a)^3 + (24 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (15 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (3 : ℝ) * a^5 * (b - c)^3 + (31 : ℝ) * a^4 * (c - a)^4 + (67 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (48 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (12 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^4 * (b - c)^4 + (34 : ℝ) * a^3 * (c - a)^5 + (91 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (84 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (30 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (3 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (21 : ℝ) * a^2 * (c - a)^6 + (66 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (75 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (36 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (6 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (3 : ℝ) * a^2 * (c - a)^2 + (3 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (3 : ℝ) * a^2 * (b - c)^2 + (7 : ℝ) * a^1 * (c - a)^7 + (25 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (33 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (19 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (4 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (3 : ℝ) * a^1 * (c - a)^3 + (3 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (6 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (3 : ℝ) * a^1 * (b - c)^3 + (1 : ℝ) * (c - a)^8 + (4 : ℝ) * (c - a)^7 * (b - c)^1 + (6 : ℝ) * (c - a)^6 * (b - c)^2 + (4 : ℝ) * (c - a)^5 * (b - c)^3 + (1 : ℝ) * (c - a)^4 * (b - c)^4 + (1 : ℝ) * (c - a)^4 + (1 : ℝ) * (c - a)^3 * (b - c)^1 + (3 : ℝ) * (c - a)^2 * (b - c)^2 + (3 : ℝ) * (c - a)^1 * (b - c)^3 + (1 : ℝ) * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^4 - a^4*b*c^3 + a^4*c^4 + a^4 - a^3*b^4*c - a^3*b - a*b^3*c^4 - a*c^3 + b^4*c^4 + b^4 - b^3*c + c^4) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^4 + 1) * (b^4 + 1) * (c^4 + 1) ≥ (a^3 * b + 1) * (b^3 * c + 1) * (c^3 * a + 1)) := @solution
#print axioms solution
