-- Prove2me | solution 1 for WorkbookSource.base_11249
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:17.973746+00:00
-- url     : https://prove2.me/submissions/630f0e47-deb2-4084-91b2-7235d3dc8be5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : 7 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (c ^ 3 + a ^ 3 + b ^ 3) + 9  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^2*b/3 + 4*a^2*c/3 + 4*a*b^2/3 - 2*a*b*c + 4*a*c^2/3 + 4*b^2*c/3 + 4*b*c^2/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^3 + (12 : ℝ) * a^2 * (b - a)^1 + (6 : ℝ) * a^2 * (c - b)^1 + (26/3 : ℝ) * a^1 * (b - a)^2 + (26/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (8/3 : ℝ) * a^1 * (c - b)^2 + (8/3 : ℝ) * (b - a)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^1 + (4/3 : ℝ) * (b - a)^1 * (c - b)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^2*b/3 + 4*a^2*c/3 + 4*a*b^2/3 - 2*a*b*c + 4*a*c^2/3 + 4*b^2*c/3 + 4*b*c^2/3) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-2*a^3 + 7*a^2 - 2*b^3 + 7*b^2 - 2*c^3 + 7*c^2 - 9) = (4*a^2*b/3 + 4*a^2*c/3 + 4*a*b^2/3 - 2*a*b*c + 4*a*c^2/3 + 4*b^2*c/3 + 4*b*c^2/3) := by
    linear_combination (-2*a^2 + 2*a*b/3 + 2*a*c/3 + a - 2*b^2 + 2*b*c/3 + b - 2*c^2 + c + 3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), 7 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (c ^ 3 + a ^ 3 + b ^ 3) + 9) := @solution
#print axioms solution
