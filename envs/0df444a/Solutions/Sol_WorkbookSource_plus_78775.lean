-- Prove2me | solution 1 for WorkbookSource.plus_78775
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:57:25.099347+00:00
-- url     : https://prove2.me/submissions/247968a8-e8d6-4215-a126-d646bd1da5d6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : a^2 / b + b^2 / c + c^2 / a + 9 * a * b * c / (a * b + b * c + c * a) ≥ 6   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b*c + a^4*c^2 - 2*a^3*b^2*c - a^3*b*c^2 + a^2*b^4 - a^2*b^3*c + 3*a^2*b^2*c^2 - 2*a^2*b*c^3 + a*b^4*c - 2*a*b^3*c^2 - a*b^2*c^3 + a*b*c^4 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^4 * (b - a)^2 + (4 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^4 * (c - b)^2 + (11 : ℝ) * a^3 * (b - a)^3 + (21 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (20 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (5 : ℝ) * a^3 * (c - b)^3 + (11 : ℝ) * a^2 * (b - a)^4 + (31 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (36 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (16 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^2 * (c - b)^4 + (5 : ℝ) * a^1 * (b - a)^5 + (18 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (25 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (15 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (b - a)^6 + (4 : ℝ) * (b - a)^5 * (c - b)^1 + (6 : ℝ) * (b - a)^4 * (c - b)^2 + (4 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b*c + a^4*c^2 - 2*a^3*b^2*c - a^3*b*c^2 + a^2*b^4 - a^2*b^3*c + 3*a^2*b^2*c^2 - 2*a^2*b*c^3 + a*b^4*c - 2*a*b^3*c^2 - a*b^2*c^3 + a*b*c^4 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^4 * (c - a)^2 + (4 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (4 : ℝ) * a^4 * (b - c)^2 + (11 : ℝ) * a^3 * (c - a)^3 + (12 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (11 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (5 : ℝ) * a^3 * (b - c)^3 + (11 : ℝ) * a^2 * (c - a)^4 + (13 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (9 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (7 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (2 : ℝ) * a^2 * (b - c)^4 + (5 : ℝ) * a^1 * (c - a)^5 + (7 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (3 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (2 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1 : ℝ) * (c - a)^6 + (2 : ℝ) * (c - a)^5 * (b - c)^1 + (1 : ℝ) * (c - a)^4 * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b*c + a^4*c^2 - 2*a^3*b^2*c - a^3*b*c^2 + a^2*b^4 - a^2*b^3*c + 3*a^2*b^2*c^2 - 2*a^2*b*c^3 + a*b^4*c - 2*a*b^3*c^2 - a*b^2*c^3 + a*b*c^4 + b^2*c^4) := by
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
  have he : (a^4*b*c + a^4*c^2 + a^3*b*c^2 + a^2*b^4 + a^2*b^3*c + 9*a^2*b^2*c^2 - 6*a^2*b^2*c - 6*a^2*b*c^2 + a*b^4*c + a*b^2*c^3 - 6*a*b^2*c^2 + a*b*c^4 + b^2*c^4) = (a^4*b*c + a^4*c^2 - 2*a^3*b^2*c - a^3*b*c^2 + a^2*b^4 - a^2*b^3*c + 3*a^2*b^2*c^2 - 2*a^2*b*c^3 + a*b^4*c - 2*a*b^3*c^2 - a*b^2*c^3 + a*b*c^4 + b^2*c^4) := by
    linear_combination (2*a^2*b^2*c + 2*a^2*b*c^2 + 2*a*b^2*c^2) * habc
  have hn : 0 ≤ (a^4*b*c + a^4*c^2 + a^3*b*c^2 + a^2*b^4 + a^2*b^3*c + 9*a^2*b^2*c^2 - 6*a^2*b^2*c - 6*a^2*b*c^2 + a*b^4*c + a*b^2*c^3 - 6*a*b^2*c^2 + a*b*c^4 + b^2*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3), a^2 / b + b^2 / c + c^2 / a + 9 * a * b * c / (a * b + b * c + c * a) ≥ 6) := @solution
#print axioms solution
