-- Prove2me | solution 1 for WorkbookSource.base_204
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:27.489591+00:00
-- url     : https://prove2.me/submissions/d9b6e951-f399-41aa-bfb5-6ea74a2d876c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) / (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b)) + 1 / 2  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2 - 2*a^4*b*c + a^4*c^2 + 2*a^3*b^3 + 2*a^3*c^3 + a^2*b^4 - 6*a^2*b^2*c^2 + a^2*c^4 - 2*a*b^4*c - 2*a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (b - a)^2 + (8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^4 * (c - b)^2 + (28 : ℝ) * a^3 * (b - a)^3 + (42 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (22 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^3 * (c - b)^3 + (36 : ℝ) * a^2 * (b - a)^4 + (72 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (42 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (6 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (20 : ℝ) * a^1 * (b - a)^5 + (50 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (40 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (10 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (13 : ℝ) * (b - a)^4 * (c - b)^2 + (6 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2 - 2*a^4*b*c + a^4*c^2 + 2*a^3*b^3 + 2*a^3*c^3 + a^2*b^4 - 6*a^2*b^2*c^2 + a^2*c^4 - 2*a*b^4*c - 2*a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
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
  have hn : 0 ≤ (a^4*b^2 - 2*a^4*b*c + a^4*c^2 + 2*a^3*b^3 + 2*a^3*c^3 + a^2*b^4 - 6*a^2*b^2*c^2 + a^2*c^4 - 2*a*b^4*c - 2*a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a) + c / (a + b)) ≥ (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) / (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b)) + 1 / 2) := @solution
#print axioms solution
