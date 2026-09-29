-- Prove2me | solution 1 for WorkbookSource.base_9129
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:40:43.507391+00:00
-- url     : https://prove2.me/submissions/326384e3-808a-4a6c-96b7-12cb528322c8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (2 * a^2 + b^2) + b^3 / (2 * b^2 + c^2) + c^3 / (2 * c^2 + a^2)) ≥ (a + b + c) / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b^2 + a^5*c^2 + 2*a^4*b^3 - 4*a^4*b^2*c - 2*a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 + 3*a^3*b^2*c^2 + 2*a^3*c^4 + a^2*b^5 - 2*a^2*b^4*c + 3*a^2*b^3*c^2 + 3*a^2*b^2*c^3 - 4*a^2*b*c^4 + 2*a^2*c^5 - 4*a*b^4*c^2 - 2*a*b^2*c^4 + 2*b^5*c^2 + 2*b^4*c^3 - 2*b^3*c^4 + b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^5 * (b - a)^2 + (6 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^5 * (c - b)^2 + (21 : ℝ) * a^4 * (b - a)^3 + (15 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (9 : ℝ) * a^4 * (c - b)^3 + (33 : ℝ) * a^3 * (b - a)^4 + (22 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (3 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (14 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (9 : ℝ) * a^3 * (c - b)^4 + (30 : ℝ) * a^2 * (b - a)^5 + (32 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (4 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (7 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (11 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (3 : ℝ) * a^2 * (c - b)^5 + (15 : ℝ) * a^1 * (b - a)^6 + (26 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (14 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (8 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (7 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (3 : ℝ) * (b - a)^7 + (7 : ℝ) * (b - a)^6 * (c - b)^1 + (6 : ℝ) * (b - a)^5 * (c - b)^2 + (4 : ℝ) * (b - a)^4 * (c - b)^3 + (3 : ℝ) * (b - a)^3 * (c - b)^4 + (1 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*b^2 + a^5*c^2 + 2*a^4*b^3 - 4*a^4*b^2*c - 2*a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 + 3*a^3*b^2*c^2 + 2*a^3*c^4 + a^2*b^5 - 2*a^2*b^4*c + 3*a^2*b^3*c^2 + 3*a^2*b^2*c^3 - 4*a^2*b*c^4 + 2*a^2*c^5 - 4*a*b^4*c^2 - 2*a*b^2*c^4 + 2*b^5*c^2 + 2*b^4*c^3 - 2*b^3*c^4 + b^2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^5 * (c - a)^2 + (6 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (6 : ℝ) * a^5 * (b - c)^2 + (21 : ℝ) * a^4 * (c - a)^3 + (48 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (45 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (9 : ℝ) * a^4 * (b - c)^3 + (33 : ℝ) * a^3 * (c - a)^4 + (110 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (135 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (58 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (9 : ℝ) * a^3 * (b - c)^4 + (30 : ℝ) * a^2 * (c - a)^5 + (118 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (176 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (113 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (31 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (3 : ℝ) * a^2 * (b - c)^5 + (15 : ℝ) * a^1 * (c - a)^6 + (64 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (109 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (88 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (32 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (4 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (3 : ℝ) * (c - a)^7 + (14 : ℝ) * (c - a)^6 * (b - c)^1 + (27 : ℝ) * (c - a)^5 * (b - c)^2 + (26 : ℝ) * (c - a)^4 * (b - c)^3 + (12 : ℝ) * (c - a)^3 * (b - c)^4 + (2 : ℝ) * (c - a)^2 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b^2 + a^5*c^2 + 2*a^4*b^3 - 4*a^4*b^2*c - 2*a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 + 3*a^3*b^2*c^2 + 2*a^3*c^4 + a^2*b^5 - 2*a^2*b^4*c + 3*a^2*b^3*c^2 + 3*a^2*b^2*c^3 - 4*a^2*b*c^4 + 2*a^2*c^5 - 4*a*b^4*c^2 - 2*a*b^2*c^4 + 2*b^5*c^2 + 2*b^4*c^3 - 2*b^3*c^4 + b^2*c^5) := by
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
  have hn : 0 ≤ (2*a^5*b^2 + a^5*c^2 + 2*a^4*b^3 - 4*a^4*b^2*c - 2*a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 + 3*a^3*b^2*c^2 + 2*a^3*c^4 + a^2*b^5 - 2*a^2*b^4*c + 3*a^2*b^3*c^2 + 3*a^2*b^2*c^3 - 4*a^2*b*c^4 + 2*a^2*c^5 - 4*a*b^4*c^2 - 2*a*b^2*c^4 + 2*b^5*c^2 + 2*b^4*c^3 - 2*b^3*c^4 + b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 / (2 * a^2 + b^2) + b^3 / (2 * b^2 + c^2) + c^3 / (2 * c^2 + a^2)) ≥ (a + b + c) / 3) := @solution
#print axioms solution
