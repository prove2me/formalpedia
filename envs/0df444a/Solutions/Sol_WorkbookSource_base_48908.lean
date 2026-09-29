-- Prove2me | solution 1 for WorkbookSource.base_48908
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:25.571333+00:00
-- url     : https://prove2.me/submissions/bd4cf839-a70b-46f8-b478-aa5ed0dbb700

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3) ^ 2 ≥ 9 * a * b * c * (a ^ 4 + b ^ 4 + c ^ 4)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7 + a^6*b + a^6*c - 9*a^5*b*c + 2*a^4*b^3 + 2*a^4*c^3 + 2*a^3*b^4 + 2*a^3*b^3*c + 2*a^3*b*c^3 + 2*a^3*c^4 + a*b^6 - 9*a*b^5*c + 2*a*b^3*c^3 - 9*a*b*c^5 + a*c^6 + b^7 + b^6*c + 2*b^4*c^3 + 2*b^3*c^4 + b*c^6 + c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^5 * (b - a)^2 + (9 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^5 * (c - b)^2 + (36 : ℝ) * a^4 * (b - a)^3 + (54 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (36 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (9 : ℝ) * a^4 * (c - b)^3 + (78 : ℝ) * a^3 * (b - a)^4 + (156 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (144 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (66 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (24 : ℝ) * a^3 * (c - b)^4 + (84 : ℝ) * a^2 * (b - a)^5 + (210 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (264 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (186 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (96 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (24 : ℝ) * a^2 * (c - b)^5 + (42 : ℝ) * a^1 * (b - a)^6 + (126 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (201 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (192 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (126 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (51 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (9 : ℝ) * a^1 * (c - b)^6 + (8 : ℝ) * (b - a)^7 + (28 : ℝ) * (b - a)^6 * (c - b)^1 + (54 : ℝ) * (b - a)^5 * (c - b)^2 + (65 : ℝ) * (b - a)^4 * (c - b)^3 + (52 : ℝ) * (b - a)^3 * (c - b)^4 + (27 : ℝ) * (b - a)^2 * (c - b)^5 + (8 : ℝ) * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7 + a^6*b + a^6*c - 9*a^5*b*c + 2*a^4*b^3 + 2*a^4*c^3 + 2*a^3*b^4 + 2*a^3*b^3*c + 2*a^3*b*c^3 + 2*a^3*c^4 + a*b^6 - 9*a*b^5*c + 2*a*b^3*c^3 - 9*a*b*c^5 + a*c^6 + b^7 + b^6*c + 2*b^4*c^3 + 2*b^3*c^4 + b*c^6 + c^7) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3) ^ 2 ≥ 9 * a * b * c * (a ^ 4 + b ^ 4 + c ^ 4)) := @solution
#print axioms solution
