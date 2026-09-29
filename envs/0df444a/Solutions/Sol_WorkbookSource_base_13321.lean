-- Prove2me | solution 1 for WorkbookSource.base_13321
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:50:57.143117+00:00
-- url     : https://prove2.me/submissions/1a08dbba-c913-4209-8b14-c342804e0fe6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :  (a^2 + 2 * b^2) * (a / c - 1) + (b^2 + 2 * c^2) * (b / a - 1) + (c^2 + 2 * a^2) * (c / b - 1) ≥ 0  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b - 3*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 3*a*b^3*c - 3*a*b*c^3 + a*c^4 + b^4*c + 2*b^2*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5 : ℝ) * a^3 * (b - a)^2 + (5 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (5 : ℝ) * a^3 * (c - b)^2 + (12 : ℝ) * a^2 * (b - a)^3 + (18 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (12 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^2 * (c - b)^3 + (10 : ℝ) * a^1 * (b - a)^4 + (20 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (15 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (5 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^1 * (c - b)^4 + (3 : ℝ) * (b - a)^5 + (7 : ℝ) * (b - a)^4 * (c - b)^1 + (6 : ℝ) * (b - a)^3 * (c - b)^2 + (2 : ℝ) * (b - a)^2 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b - 3*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 3*a*b^3*c - 3*a*b*c^3 + a*c^4 + b^4*c + 2*b^2*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (5 : ℝ) * a^3 * (c - a)^2 + (5 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (5 : ℝ) * a^3 * (b - c)^2 + (12 : ℝ) * a^2 * (c - a)^3 + (18 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (12 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (3 : ℝ) * a^2 * (b - c)^3 + (10 : ℝ) * a^1 * (c - a)^4 + (20 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (15 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (5 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^1 * (b - c)^4 + (3 : ℝ) * (c - a)^5 + (8 : ℝ) * (c - a)^4 * (b - c)^1 + (8 : ℝ) * (c - a)^3 * (b - c)^2 + (4 : ℝ) * (c - a)^2 * (b - c)^3 + (1 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b - 3*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 3*a*b^3*c - 3*a*b*c^3 + a*c^4 + b^4*c + 2*b^2*c^3) := by
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
  have hn : 0 ≤ (a^4*b - 3*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 3*a*b^3*c - 3*a*b*c^3 + a*c^4 + b^4*c + 2*b^2*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a^2 + 2 * b^2) * (a / c - 1) + (b^2 + 2 * c^2) * (b / a - 1) + (c^2 + 2 * a^2) * (c / b - 1) ≥ 0) := @solution
#print axioms solution
