-- Prove2me | solution 1 for WorkbookSource.base_11000
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:17.196619+00:00
-- url     : https://prove2.me/submissions/b6f7235d-638d-47bc-b172-737d9821afea

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 6 ≥ 27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 + 6*a^5*b + 6*a^5*c - 12*a^4*b^2 - 24*a^4*b*c - 12*a^4*c^2 + 20*a^3*b^3 + 6*a^3*b^2*c + 6*a^3*b*c^2 + 20*a^3*c^3 - 12*a^2*b^4 + 6*a^2*b^3*c + 9*a^2*b^2*c^2 + 6*a^2*b*c^3 - 12*a^2*c^4 + 6*a*b^5 - 24*a*b^4*c + 6*a*b^3*c^2 + 6*a*b^2*c^3 - 24*a*b*c^4 + 6*a*c^5 + b^6 + 6*b^5*c - 12*b^4*c^2 + 20*b^3*c^3 - 12*b^2*c^4 + 6*b*c^5 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * a^2 * (b - a)^4 + (54 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (81 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (54 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (27 : ℝ) * a^2 * (c - b)^4 + (36 : ℝ) * a^1 * (b - a)^5 + (90 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (144 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (126 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (72 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * a^1 * (c - b)^5 + (10 : ℝ) * (b - a)^6 + (30 : ℝ) * (b - a)^5 * (c - b)^1 + (51 : ℝ) * (b - a)^4 * (c - b)^2 + (52 : ℝ) * (b - a)^3 * (c - b)^3 + (33 : ℝ) * (b - a)^2 * (c - b)^4 + (12 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 + 6*a^5*b + 6*a^5*c - 12*a^4*b^2 - 24*a^4*b*c - 12*a^4*c^2 + 20*a^3*b^3 + 6*a^3*b^2*c + 6*a^3*b*c^2 + 20*a^3*c^3 - 12*a^2*b^4 + 6*a^2*b^3*c + 9*a^2*b^2*c^2 + 6*a^2*b*c^3 - 12*a^2*c^4 + 6*a*b^5 - 24*a*b^4*c + 6*a*b^3*c^2 + 6*a*b^2*c^3 - 24*a*b*c^4 + 6*a*c^5 + b^6 + 6*b^5*c - 12*b^4*c^2 + 20*b^3*c^3 - 12*b^2*c^4 + 6*b*c^5 + c^6) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + c) ^ 6 ≥ 27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2) := @solution
#print axioms solution
