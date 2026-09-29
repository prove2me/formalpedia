-- Prove2me | solution 1 for WorkbookSource.plus_32509
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:35:52.129887+00:00
-- url     : https://prove2.me/submissions/dbb058ff-b2a0-417a-8ca6-373b13a69c22

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a^2 * b^4 + b^2 * c^4 + c^2 * a^4) + a * b * c * (a^3 + b^3 + c^3) + (a^3 * b^3 + b^3 * c^3 + c^3 * a^3) ≥ 9 * a^2 * b^2 * c^2 + a * b * c * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b*c + 3*a^4*c^2 + a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + a^3*c^3 + 3*a^2*b^4 - a^2*b^3*c - 9*a^2*b^2*c^2 - a^2*b*c^3 + a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + a*b*c^4 + b^3*c^3 + 3*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^4 * (b - a)^2 + (16 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^4 * (c - b)^2 + (48 : ℝ) * a^3 * (b - a)^3 + (84 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (68 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (16 : ℝ) * a^3 * (c - b)^3 + (52 : ℝ) * a^2 * (b - a)^4 + (128 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (120 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (44 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (24 : ℝ) * a^1 * (b - a)^5 + (75 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (86 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (42 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (7 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (15 : ℝ) * (b - a)^5 * (c - b)^1 + (21 : ℝ) * (b - a)^4 * (c - b)^2 + (13 : ℝ) * (b - a)^3 * (c - b)^3 + (3 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b*c + 3*a^4*c^2 + a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + a^3*c^3 + 3*a^2*b^4 - a^2*b^3*c - 9*a^2*b^2*c^2 - a^2*b*c^3 + a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + a*b*c^4 + b^3*c^3 + 3*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^4 * (c - a)^2 + (16 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (16 : ℝ) * a^4 * (b - c)^2 + (48 : ℝ) * a^3 * (c - a)^3 + (60 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (44 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (16 : ℝ) * a^3 * (b - c)^3 + (52 : ℝ) * a^2 * (c - a)^4 + (80 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (48 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (20 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^2 * (b - c)^4 + (24 : ℝ) * a^1 * (c - a)^5 + (45 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (26 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (6 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * (c - a)^6 + (9 : ℝ) * (c - a)^5 * (b - c)^1 + (6 : ℝ) * (c - a)^4 * (b - c)^2 + (1 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b*c + 3*a^4*c^2 + a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + a^3*c^3 + 3*a^2*b^4 - a^2*b^3*c - 9*a^2*b^2*c^2 - a^2*b*c^3 + a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + a*b*c^4 + b^3*c^3 + 3*b^2*c^4) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 3 * (a^2 * b^4 + b^2 * c^4 + c^2 * a^4) + a * b * c * (a^3 + b^3 + c^3) + (a^3 * b^3 + b^3 * c^3 + c^3 * a^3) ≥ 9 * a^2 * b^2 * c^2 + a * b * c * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a))) := @solution
#print axioms solution
