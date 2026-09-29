-- Prove2me | solution 1 for WorkbookSource.base_50202
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:39:51.891572+00:00
-- url     : https://prove2.me/submissions/27316cad-edca-409a-9a1b-e37cd1f9bdc3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 3 * a * b * c ≥ 9 + (a * b * c * (a * b + b * c + c * a - 3 * a * b * c)) / (6 * (a * b + b * c + c * a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b/3 + 2*a^5*c/3 + 2*a^4*b*c/3 - 4*a^3*b^3/3 - a^3*b^2*c - a^3*b*c^2 - 4*a^3*c^3/3 - a^2*b^3*c + 4*a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^5/3 + 2*a*b^4*c/3 - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4/3 + 2*a*c^5/3 + 2*b^5*c/3 - 4*b^3*c^3/3 + 2*b*c^5/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^4 * (b - a)^2 + (16/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16/3 : ℝ) * a^4 * (c - b)^2 + (10 : ℝ) * a^3 * (b - a)^3 + (15 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (83/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (34/3 : ℝ) * a^3 * (c - b)^3 + (16/3 : ℝ) * a^2 * (b - a)^4 + (32/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (37 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (95/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (22/3 : ℝ) * a^2 * (c - b)^4 + (2/3 : ℝ) * a^1 * (b - a)^5 + (5/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (52/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (73/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (32/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/3 : ℝ) * a^1 * (c - b)^5 + (8/3 : ℝ) * (b - a)^4 * (c - b)^2 + (16/3 : ℝ) * (b - a)^3 * (c - b)^3 + (10/3 : ℝ) * (b - a)^2 * (c - b)^4 + (2/3 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b/3 + 2*a^5*c/3 + 2*a^4*b*c/3 - 4*a^3*b^3/3 - a^3*b^2*c - a^3*b*c^2 - 4*a^3*c^3/3 - a^2*b^3*c + 4*a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^5/3 + 2*a*b^4*c/3 - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4/3 + 2*a*c^5/3 + 2*b^5*c/3 - 4*b^3*c^3/3 + 2*b*c^5/3) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (12*a^3*b + 12*a^3*c + 3*a^2*b^2*c^2 + 17*a^2*b^2*c + 17*a^2*b*c^2 + 12*a^2*b*c + 12*a*b^3 + 17*a*b^2*c^2 + 12*a*b^2*c + 12*a*b*c^2 - 54*a*b + 12*a*c^3 - 54*a*c + 12*b^3*c + 12*b*c^3 - 54*b*c) = (2*a^5*b/3 + 2*a^5*c/3 + 2*a^4*b*c/3 - 4*a^3*b^3/3 - a^3*b^2*c - a^3*b*c^2 - 4*a^3*c^3/3 - a^2*b^3*c + 4*a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^5/3 + 2*a*b^4*c/3 - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4/3 + 2*a*c^5/3 + 2*b^5*c/3 - 4*b^3*c^3/3 + 2*b*c^5/3) := by
    linear_combination (-2*a^4*b/3 - 2*a^4*c/3 + 2*a^3*b^2/3 + 2*a^3*b*c/3 - 2*a^3*b + 2*a^3*c^2/3 - 2*a^3*c + 2*a^2*b^3/3 - a^2*b^2*c/3 + 4*a^2*b^2 - a^2*b*c^2/3 + 6*a^2*b*c + 6*a^2*b + 2*a^2*c^3/3 + 4*a^2*c^2 + 6*a^2*c - 2*a*b^4/3 + 2*a*b^3*c/3 - 2*a*b^3 - a*b^2*c^2/3 + 6*a*b^2*c + 6*a*b^2 + 2*a*b*c^3/3 + 6*a*b*c^2 + 18*a*b*c + 18*a*b - 2*a*c^4/3 - 2*a*c^3 + 6*a*c^2 + 18*a*c - 2*b^4*c/3 + 2*b^3*c^2/3 - 2*b^3*c + 2*b^2*c^3/3 + 4*b^2*c^2 + 6*b^2*c - 2*b*c^4/3 - 2*b*c^3 + 6*b*c^2 + 18*b*c) * habc
  have hn : 0 ≤ (12*a^3*b + 12*a^3*c + 3*a^2*b^2*c^2 + 17*a^2*b^2*c + 17*a^2*b*c^2 + 12*a^2*b*c + 12*a*b^3 + 17*a*b^2*c^2 + 12*a*b^2*c + 12*a*b*c^2 - 54*a*b + 12*a*c^3 - 54*a*c + 12*b^3*c + 12*b*c^3 - 54*b*c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 3 * a * b * c ≥ 9 + (a * b * c * (a * b + b * c + c * a - 3 * a * b * c)) / (6 * (a * b + b * c + c * a))) := @solution
#print axioms solution
