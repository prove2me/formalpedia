-- Prove2me | solution 1 for WorkbookSource.plus_74668
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:27.711756+00:00
-- url     : https://prove2.me/submissions/47706d97-4ce2-4404-9a52-53d7951b82bd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (a + b) + 1 / ((a + b) * c) + 1 / (a * b * c) ≥ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4/27 + 7*a^3*b/27 + a^3*c/9 + 4*a^2*b^2/9 - 10*a^2*b*c/9 + a^2*c^2/9 + 7*a*b^3/27 - 10*a*b^2*c/9 + 2*a*b*c^2/3 + a*c^3/27 + b^4/27 + b^3*c/9 + b^2*c^2/9 + b*c^3/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (7/9 : ℝ) * a^2 * (b - a)^2 + (10/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (10/9 : ℝ) * a^2 * (c - b)^2 + (28/27 : ℝ) * a^1 * (b - a)^3 + (5/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (11/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (2/27 : ℝ) * a^1 * (c - b)^3 + (8/27 : ℝ) * (b - a)^4 + (4/9 : ℝ) * (b - a)^3 * (c - b)^1 + (2/9 : ℝ) * (b - a)^2 * (c - b)^2 + (1/27 : ℝ) * (b - a)^1 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4/27 + 7*a^3*b/27 + a^3*c/9 + 4*a^2*b^2/9 - 10*a^2*b*c/9 + a^2*c^2/9 + 7*a*b^3/27 - 10*a*b^2*c/9 + 2*a*b*c^2/3 + a*c^3/27 + b^4/27 + b^3*c/9 + b^2*c^2/9 + b*c^3/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (7/9 : ℝ) * a^2 * (c - a)^2 + (4/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (7/9 : ℝ) * a^2 * (b - c)^2 + (28/27 : ℝ) * a^1 * (c - a)^3 + (13/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (14/27 : ℝ) * a^1 * (b - c)^3 + (8/27 : ℝ) * (c - a)^4 + (20/27 : ℝ) * (c - a)^3 * (b - c)^1 + (2/3 : ℝ) * (c - a)^2 * (b - c)^2 + (7/27 : ℝ) * (c - a)^1 * (b - c)^3 + (1/27 : ℝ) * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ c) (hord1 : c ≤ a) (hord2 : a ≤ b) : 0 ≤ (a^4/27 + 7*a^3*b/27 + a^3*c/9 + 4*a^2*b^2/9 - 10*a^2*b*c/9 + a^2*c^2/9 + 7*a*b^3/27 - 10*a*b^2*c/9 + 2*a*b*c^2/3 + a*c^3/27 + b^4/27 + b^3*c/9 + b^2*c^2/9 + b*c^3/27) := by
    have hdiff1 : 0 ≤ (a - c) := by linarith
    have hdiff2 : 0 ≤ (b - a) := by linarith
    have hpos : 0 ≤ (10/9 : ℝ) * c^2 * (a - c)^2 + (10/9 : ℝ) * c^2 * (a - c)^1 * (b - a)^1 + (7/9 : ℝ) * c^2 * (b - a)^2 + (58/27 : ℝ) * c^1 * (a - c)^3 + (29/9 : ℝ) * c^1 * (a - c)^2 * (b - a)^1 + (19/9 : ℝ) * c^1 * (a - c)^1 * (b - a)^2 + (14/27 : ℝ) * c^1 * (b - a)^3 + (28/27 : ℝ) * (a - c)^4 + (56/27 : ℝ) * (a - c)^3 * (b - a)^1 + (13/9 : ℝ) * (a - c)^2 * (b - a)^2 + (11/27 : ℝ) * (a - c)^1 * (b - a)^3 + (1/27 : ℝ) * (b - a)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4/27 + 7*a^3*b/27 + a^3*c/9 + 4*a^2*b^2/9 - 10*a^2*b*c/9 + a^2*c^2/9 + 7*a*b^3/27 - 10*a*b^2*c/9 + 2*a*b*c^2/3 + a*c^3/27 + b^4/27 + b^3*c/9 + b^2*c^2/9 + b*c^3/27) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux1 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-2*a^2*b*c - 2*a*b^2*c + a*b*c + a*b + a + b) = (a^4/27 + 7*a^3*b/27 + a^3*c/9 + 4*a^2*b^2/9 - 10*a^2*b*c/9 + a^2*c^2/9 + 7*a*b^3/27 - 10*a*b^2*c/9 + 2*a*b*c^2/3 + a*c^3/27 + b^4/27 + b^3*c/9 + b^2*c^2/9 + b*c^3/27) := by
    linear_combination (-a^3/27 - 2*a^2*b/9 - 2*a^2*c/27 - a^2/9 - 2*a*b^2/9 - 16*a*b*c/27 - 5*a*b/9 - a*c^2/27 - a*c/9 - a/3 - b^3/27 - 2*b^2*c/27 - b^2/9 - b*c^2/27 - b*c/9 - b/3) * hab
  have hn : 0 ≤ (-2*a^2*b*c - 2*a*b^2*c + a*b*c + a*b + a + b) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), 1 / (a + b) + 1 / ((a + b) * c) + 1 / (a * b * c) ≥ 2) := @solution
#print axioms solution
