-- Prove2me | solution 1 for WorkbookSource.base_56810
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:33.019573+00:00
-- url     : https://prove2.me/submissions/bd2575e2-383c-41e0-bcea-f247a2d55021

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 * b + b^3 * c + c^3 * a) * (a + b + c) ≥ 3 * a * b * c * (a^2 + b^2 + c^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b + a^3*b^2 - 2*a^3*b*c + a^2*c^3 - 2*a*b^3*c - 2*a*b*c^3 + a*c^4 + b^4*c + b^3*c^2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^3 * (b - a)^2 + (4 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^3 * (c - b)^2 + (9 : ℝ) * a^2 * (b - a)^3 + (9 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (6 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^2 * (c - b)^3 + (7 : ℝ) * a^1 * (b - a)^4 + (8 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^1 * (c - b)^4 + (2 : ℝ) * (b - a)^5 + (3 : ℝ) * (b - a)^4 * (c - b)^1 + (1 : ℝ) * (b - a)^3 * (c - b)^2 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b + a^3*b^2 - 2*a^3*b*c + a^2*c^3 - 2*a*b^3*c - 2*a*b*c^3 + a*c^4 + b^4*c + b^3*c^2) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^3 * (c - a)^2 + (4 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (4 : ℝ) * a^3 * (b - c)^2 + (9 : ℝ) * a^2 * (c - a)^3 + (18 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (15 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (3 : ℝ) * a^2 * (b - c)^3 + (7 : ℝ) * a^1 * (c - a)^4 + (20 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (21 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (8 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^1 * (b - c)^4 + (2 : ℝ) * (c - a)^5 + (7 : ℝ) * (c - a)^4 * (b - c)^1 + (9 : ℝ) * (c - a)^3 * (b - c)^2 + (5 : ℝ) * (c - a)^2 * (b - c)^3 + (1 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b + a^3*b^2 - 2*a^3*b*c + a^2*c^3 - 2*a*b^3*c - 2*a*b*c^3 + a*c^4 + b^4*c + b^3*c^2) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 * b + b^3 * c + c^3 * a) * (a + b + c) ≥ 3 * a * b * c * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
