-- Prove2me | solution 1 for WorkbookSource.plus_56151
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:40:39.450245+00:00
-- url     : https://prove2.me/submissions/a2e0ca49-bf41-4538-819e-1dc1f3a97ad3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 4 * (a ^ 2 + a * b + c ^ 2) * (b ^ 2 + b * c + a ^ 2) * (c ^ 2 + c * a + b ^ 2) ≥ 3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b) ^ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*c + a^4*b^2 - 2*a^4*b*c + a^4*c^2 - 2*a^3*b^3 - 2*a^3*b^2*c + 2*a^3*b*c^2 - 2*a^3*c^3 + a^2*b^4 + 2*a^2*b^3*c - 6*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*c^4 + 4*a*b^5 - 2*a*b^4*c - 2*a*b^3*c^2 + 2*a*b^2*c^3 - 2*a*b*c^4 + b^4*c^2 - 2*b^3*c^3 + b^2*c^4 + 4*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^4 * (b - a)^2 + (24 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^4 * (c - b)^2 + (60 : ℝ) * a^3 * (b - a)^3 + (112 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (124 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (36 : ℝ) * a^3 * (c - b)^3 + (56 : ℝ) * a^2 * (b - a)^4 + (156 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (216 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (116 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (20 : ℝ) * a^2 * (c - b)^4 + (24 : ℝ) * a^1 * (b - a)^5 + (92 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (156 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (120 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (40 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (4 : ℝ) * (b - a)^6 + (20 : ℝ) * (b - a)^5 * (c - b)^1 + (41 : ℝ) * (b - a)^4 * (c - b)^2 + (42 : ℝ) * (b - a)^3 * (c - b)^3 + (21 : ℝ) * (b - a)^2 * (c - b)^4 + (4 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^5*c + a^4*b^2 - 2*a^4*b*c + a^4*c^2 - 2*a^3*b^3 - 2*a^3*b^2*c + 2*a^3*b*c^2 - 2*a^3*c^3 + a^2*b^4 + 2*a^2*b^3*c - 6*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*c^4 + 4*a*b^5 - 2*a*b^4*c - 2*a*b^3*c^2 + 2*a*b^2*c^3 - 2*a*b*c^4 + b^4*c^2 - 2*b^3*c^3 + b^2*c^4 + 4*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^4 * (c - a)^2 + (24 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (24 : ℝ) * a^4 * (b - c)^2 + (60 : ℝ) * a^3 * (c - a)^3 + (68 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (80 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (36 : ℝ) * a^3 * (b - c)^3 + (56 : ℝ) * a^2 * (c - a)^4 + (68 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (84 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (72 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (20 : ℝ) * a^2 * (b - c)^4 + (24 : ℝ) * a^1 * (c - a)^5 + (28 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (28 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (36 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (20 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * a^1 * (b - c)^5 + (4 : ℝ) * (c - a)^6 + (4 : ℝ) * (c - a)^5 * (b - c)^1 + (1 : ℝ) * (c - a)^4 * (b - c)^2 + (2 : ℝ) * (c - a)^3 * (b - c)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*c + a^4*b^2 - 2*a^4*b*c + a^4*c^2 - 2*a^3*b^3 - 2*a^3*b^2*c + 2*a^3*b*c^2 - 2*a^3*c^3 + a^2*b^4 + 2*a^2*b^3*c - 6*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*c^4 + 4*a*b^5 - 2*a*b^4*c - 2*a*b^3*c^2 + 2*a*b^2*c^3 - 2*a*b*c^4 + b^4*c^2 - 2*b^3*c^3 + b^2*c^4 + 4*b*c^5) := by
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
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), 4 * (a ^ 2 + a * b + c ^ 2) * (b ^ 2 + b * c + a ^ 2) * (c ^ 2 + c * a + b ^ 2) ≥ 3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b) ^ 2) := @solution
#print axioms solution
