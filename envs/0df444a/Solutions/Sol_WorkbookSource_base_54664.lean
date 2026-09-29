-- Prove2me | solution 1 for WorkbookSource.base_54664
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:16:49.521784+00:00
-- url     : https://prove2.me/submissions/0d3398c1-5bbb-4eb4-8aec-f2a1ed31ec6b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (c + 2 * a) / b + (a + 2 * b) / c + (b + 2 * c) / a ≥ (3 * a + 4 * c - b) / (a + b) + (3 * b + 4 * a - c) / (b + c) + (3 * c + 4 * b - a) / (c + a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2 - a^4*b*c + 2*a^4*c^2 + 3*a^3*b^3 - 3*a^3*b^2*c + a^3*b*c^2 + 3*a^3*c^3 + 2*a^2*b^4 + a^2*b^3*c - 9*a^2*b^2*c^2 - 3*a^2*b*c^3 + a^2*c^4 - a*b^4*c - 3*a*b^3*c^2 + a*b^2*c^3 - a*b*c^4 + b^4*c^2 + 3*b^3*c^3 + 2*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^4 * (b - a)^2 + (16 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^4 * (c - b)^2 + (52 : ℝ) * a^3 * (b - a)^3 + (84 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (56 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^3 * (c - b)^3 + (62 : ℝ) * a^2 * (b - a)^4 + (136 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (102 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (28 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^2 * (c - b)^4 + (32 : ℝ) * a^1 * (b - a)^5 + (87 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (82 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (30 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * (b - a)^6 + (19 : ℝ) * (b - a)^5 * (c - b)^1 + (22 : ℝ) * (b - a)^4 * (c - b)^2 + (11 : ℝ) * (b - a)^3 * (c - b)^3 + (2 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b^2 - a^4*b*c + 2*a^4*c^2 + 3*a^3*b^3 - 3*a^3*b^2*c + a^3*b*c^2 + 3*a^3*c^3 + 2*a^2*b^4 + a^2*b^3*c - 9*a^2*b^2*c^2 - 3*a^2*b*c^3 + a^2*c^4 - a*b^4*c - 3*a*b^3*c^2 + a*b^2*c^3 - a*b*c^4 + b^4*c^2 + 3*b^3*c^3 + 2*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^4 * (c - a)^2 + (16 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (16 : ℝ) * a^4 * (b - c)^2 + (52 : ℝ) * a^3 * (c - a)^3 + (72 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (44 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (12 : ℝ) * a^3 * (b - c)^3 + (62 : ℝ) * a^2 * (c - a)^4 + (112 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (66 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (16 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (2 : ℝ) * a^2 * (b - c)^4 + (32 : ℝ) * a^1 * (c - a)^5 + (73 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (54 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (14 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (6 : ℝ) * (c - a)^6 + (17 : ℝ) * (c - a)^5 * (b - c)^1 + (17 : ℝ) * (c - a)^4 * (b - c)^2 + (7 : ℝ) * (c - a)^3 * (b - c)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2 - a^4*b*c + 2*a^4*c^2 + 3*a^3*b^3 - 3*a^3*b^2*c + a^3*b*c^2 + 3*a^3*c^3 + 2*a^2*b^4 + a^2*b^3*c - 9*a^2*b^2*c^2 - 3*a^2*b*c^3 + a^2*c^4 - a*b^4*c - 3*a*b^3*c^2 + a*b^2*c^3 - a*b*c^4 + b^4*c^2 + 3*b^3*c^3 + 2*b^2*c^4) := by
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
  have hn : 0 ≤ (a^4*b^2 - a^4*b*c + 2*a^4*c^2 + 3*a^3*b^3 - 3*a^3*b^2*c + a^3*b*c^2 + 3*a^3*c^3 + 2*a^2*b^4 + a^2*b^3*c - 9*a^2*b^2*c^2 - 3*a^2*b*c^3 + a^2*c^4 - a*b^4*c - 3*a*b^3*c^2 + a*b^2*c^3 - a*b*c^4 + b^4*c^2 + 3*b^3*c^3 + 2*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (c + 2 * a) / b + (a + 2 * b) / c + (b + 2 * c) / a ≥ (3 * a + 4 * c - b) / (a + b) + (3 * b + 4 * a - c) / (b + c) + (3 * c + 4 * b - a) / (c + a)) := @solution
#print axioms solution
