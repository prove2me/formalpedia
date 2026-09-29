-- Prove2me | solution 1 for WorkbookSource.plus_46295
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:38:13.701983+00:00
-- url     : https://prove2.me/submissions/889c2004-b20d-4880-8fd2-2f954c72d64a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + 2 * b) ^ 2 * (b + 2 * c) ^ 2 * (c + 2 * a) ^ 2 ≥ 27 * a * b * c * (a + 2 * c) * (b + 2 * a) * (c + 2 * b)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4*b^2 + 16*a^4*b*c + 16*a^4*c^2 + 16*a^3*b^3 - 40*a^3*b^2*c + 26*a^3*b*c^2 + 16*a^3*c^3 + 16*a^2*b^4 + 26*a^2*b^3*c - 114*a^2*b^2*c^2 - 40*a^2*b*c^3 + 4*a^2*c^4 + 16*a*b^4*c - 40*a*b^3*c^2 + 26*a*b^2*c^3 + 16*a*b*c^4 + 4*b^4*c^2 + 16*b^3*c^3 + 16*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (162 : ℝ) * a^4 * (b - a)^2 + (162 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (162 : ℝ) * a^4 * (c - b)^2 + (486 : ℝ) * a^3 * (b - a)^3 + (810 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (648 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (162 : ℝ) * a^3 * (c - b)^3 + (522 : ℝ) * a^2 * (b - a)^4 + (1206 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1080 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (396 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (36 : ℝ) * a^2 * (c - b)^4 + (234 : ℝ) * a^1 * (b - a)^5 + (678 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (726 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (330 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (48 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (36 : ℝ) * (b - a)^6 + (120 : ℝ) * (b - a)^5 * (c - b)^1 + (148 : ℝ) * (b - a)^4 * (c - b)^2 + (80 : ℝ) * (b - a)^3 * (c - b)^3 + (16 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^4*b^2 + 16*a^4*b*c + 16*a^4*c^2 + 16*a^3*b^3 - 40*a^3*b^2*c + 26*a^3*b*c^2 + 16*a^3*c^3 + 16*a^2*b^4 + 26*a^2*b^3*c - 114*a^2*b^2*c^2 - 40*a^2*b*c^3 + 4*a^2*c^4 + 16*a*b^4*c - 40*a*b^3*c^2 + 26*a*b^2*c^3 + 16*a*b*c^4 + 4*b^4*c^2 + 16*b^3*c^3 + 16*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (162 : ℝ) * a^4 * (c - a)^2 + (162 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (162 : ℝ) * a^4 * (b - c)^2 + (486 : ℝ) * a^3 * (c - a)^3 + (648 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (486 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (162 : ℝ) * a^3 * (b - c)^3 + (522 : ℝ) * a^2 * (c - a)^4 + (882 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (594 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (234 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (36 : ℝ) * a^2 * (b - c)^4 + (234 : ℝ) * a^1 * (c - a)^5 + (492 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (354 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (120 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (24 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (36 : ℝ) * (c - a)^6 + (96 : ℝ) * (c - a)^5 * (b - c)^1 + (88 : ℝ) * (c - a)^4 * (b - c)^2 + (32 : ℝ) * (c - a)^3 * (b - c)^3 + (4 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4*b^2 + 16*a^4*b*c + 16*a^4*c^2 + 16*a^3*b^3 - 40*a^3*b^2*c + 26*a^3*b*c^2 + 16*a^3*c^3 + 16*a^2*b^4 + 26*a^2*b^3*c - 114*a^2*b^2*c^2 - 40*a^2*b*c^3 + 4*a^2*c^4 + 16*a*b^4*c - 40*a*b^3*c^2 + 26*a*b^2*c^3 + 16*a*b*c^4 + 4*b^4*c^2 + 16*b^3*c^3 + 16*b^2*c^4) := by
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
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), (a + 2 * b) ^ 2 * (b + 2 * c) ^ 2 * (c + 2 * a) ^ 2 ≥ 27 * a * b * c * (a + 2 * c) * (b + 2 * a) * (c + 2 * b)) := @solution
#print axioms solution
