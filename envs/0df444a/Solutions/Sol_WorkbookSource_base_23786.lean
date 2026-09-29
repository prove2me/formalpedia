-- Prove2me | solution 1 for WorkbookSource.base_23786
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:00:08.725263+00:00
-- url     : https://prove2.me/submissions/7f53403e-b044-46a9-aa84-2d6ae4010ed4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 27 / 2 ≥ 4 * (a * b + b * c + c * a) + a ^ 2 * b ^ 2 / (a + b) + b ^ 2 * c ^ 2 / (b + c) + c ^ 2 * a ^ 2 / (a + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b + a^5*c + 4*a^4*b^2/3 + 8*a^4*b*c/3 + 4*a^4*c^2/3 - 4*a^3*b^3/3 - 5*a^3*b^2*c/3 - 5*a^3*b*c^2/3 - 4*a^3*c^3/3 + 4*a^2*b^4/3 - 5*a^2*b^3*c/3 - 8*a^2*b^2*c^2 - 5*a^2*b*c^3/3 + 4*a^2*c^4/3 + a*b^5 + 8*a*b^4*c/3 - 5*a*b^3*c^2/3 - 5*a*b^2*c^3/3 + 8*a*b*c^4/3 + a*c^5 + b^5*c + 4*b^4*c^2/3 - 4*b^3*c^3/3 + 4*b^2*c^4/3 + b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (76/3 : ℝ) * a^4 * (b - a)^2 + (76/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (76/3 : ℝ) * a^4 * (c - b)^2 + (66 : ℝ) * a^3 * (b - a)^3 + (99 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (311/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (106/3 : ℝ) * a^3 * (c - b)^3 + (184/3 : ℝ) * a^2 * (b - a)^4 + (368/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (145 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (251/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (46/3 : ℝ) * a^2 * (c - b)^4 + (24 : ℝ) * a^1 * (b - a)^5 + (60 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (242/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (61 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (61/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (10/3 : ℝ) * (b - a)^6 + (10 : ℝ) * (b - a)^5 * (c - b)^1 + (46/3 : ℝ) * (b - a)^4 * (c - b)^2 + (14 : ℝ) * (b - a)^3 * (c - b)^3 + (19/3 : ℝ) * (b - a)^2 * (c - b)^4 + (1 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b + a^5*c + 4*a^4*b^2/3 + 8*a^4*b*c/3 + 4*a^4*c^2/3 - 4*a^3*b^3/3 - 5*a^3*b^2*c/3 - 5*a^3*b*c^2/3 - 4*a^3*c^3/3 + 4*a^2*b^4/3 - 5*a^2*b^3*c/3 - 8*a^2*b^2*c^2 - 5*a^2*b*c^3/3 + 4*a^2*c^4/3 + a*b^5 + 8*a*b^4*c/3 - 5*a*b^3*c^2/3 - 5*a*b^2*c^3/3 + 8*a*b*c^4/3 + a*c^5 + b^5*c + 4*b^4*c^2/3 - 4*b^3*c^3/3 + 4*b^2*c^4/3 + b*c^5) := by
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
  have he : (-2*a^3*b^3 - 2*a^3*b^2*c - 8*a^3*b^2 - 2*a^3*b*c^2 - 16*a^3*b*c - 2*a^3*c^3 - 8*a^3*c^2 - 2*a^2*b^3*c - 8*a^2*b^3 - 6*a^2*b^2*c^2 - 32*a^2*b^2*c - 2*a^2*b*c^3 - 32*a^2*b*c^2 + 27*a^2*b - 8*a^2*c^3 + 27*a^2*c - 2*a*b^3*c^2 - 16*a*b^3*c - 2*a*b^2*c^3 - 32*a*b^2*c^2 + 27*a*b^2 - 16*a*b*c^3 + 54*a*b*c + 27*a*c^2 - 2*b^3*c^3 - 8*b^3*c^2 - 8*b^2*c^3 + 27*b^2*c + 27*b*c^2) = (a^5*b + a^5*c + 4*a^4*b^2/3 + 8*a^4*b*c/3 + 4*a^4*c^2/3 - 4*a^3*b^3/3 - 5*a^3*b^2*c/3 - 5*a^3*b*c^2/3 - 4*a^3*c^3/3 + 4*a^2*b^4/3 - 5*a^2*b^3*c/3 - 8*a^2*b^2*c^2 - 5*a^2*b*c^3/3 + 4*a^2*c^4/3 + a*b^5 + 8*a*b^4*c/3 - 5*a*b^3*c^2/3 - 5*a*b^2*c^3/3 + 8*a*b*c^4/3 + a*c^5 + b^5*c + 4*b^4*c^2/3 - 4*b^3*c^3/3 + 4*b^2*c^4/3 + b*c^5) := by
    linear_combination (-a^4*b - a^4*c - a^3*b^2/3 - 2*a^3*b*c/3 - 3*a^3*b - a^3*c^2/3 - 3*a^3*c - a^2*b^3/3 + 2*a^2*b^2*c/3 - 6*a^2*b^2 + 2*a^2*b*c^2/3 - 12*a^2*b*c - 9*a^2*b - a^2*c^3/3 - 6*a^2*c^2 - 9*a^2*c - a*b^4 - 2*a*b^3*c/3 - 3*a*b^3 + 2*a*b^2*c^2/3 - 12*a*b^2*c - 9*a*b^2 - 2*a*b*c^3/3 - 12*a*b*c^2 - 18*a*b*c - a*c^4 - 3*a*c^3 - 9*a*c^2 - b^4*c - b^3*c^2/3 - 3*b^3*c - b^2*c^3/3 - 6*b^2*c^2 - 9*b^2*c - b*c^4 - 3*b*c^3 - 9*b*c^2) * habc
  have hn : 0 ≤ (-2*a^3*b^3 - 2*a^3*b^2*c - 8*a^3*b^2 - 2*a^3*b*c^2 - 16*a^3*b*c - 2*a^3*c^3 - 8*a^3*c^2 - 2*a^2*b^3*c - 8*a^2*b^3 - 6*a^2*b^2*c^2 - 32*a^2*b^2*c - 2*a^2*b*c^3 - 32*a^2*b*c^2 + 27*a^2*b - 8*a^2*c^3 + 27*a^2*c - 2*a*b^3*c^2 - 16*a*b^3*c - 2*a*b^2*c^3 - 32*a*b^2*c^2 + 27*a*b^2 - 16*a*b*c^3 + 54*a*b*c + 27*a*c^2 - 2*b^3*c^3 - 8*b^3*c^2 - 8*b^2*c^3 + 27*b^2*c + 27*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 27 / 2 ≥ 4 * (a * b + b * c + c * a) + a ^ 2 * b ^ 2 / (a + b) + b ^ 2 * c ^ 2 / (b + c) + c ^ 2 * a ^ 2 / (a + c)) := @solution
#print axioms solution
