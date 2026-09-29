-- Prove2me | solution 1 for WorkbookSource.plus_66050
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:27.177061+00:00
-- url     : https://prove2.me/submissions/3854e95d-c4f7-47f2-96e4-e6cc40ef6848

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 / (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + 30 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 ≥ 19   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5 + 16*a^4*b + 5*a^4*c - 28*a^3*b^2 - 18*a^3*b*c + 21*a^3*c^2 + 21*a^2*b^3 + 3*a^2*b^2*c + 3*a^2*b*c^2 - 28*a^2*c^3 + 5*a*b^4 - 18*a*b^3*c + 3*a*b^2*c^2 - 18*a*b*c^3 + 16*a*c^4 + b^5 + 16*b^4*c - 28*b^3*c^2 + 21*b^2*c^3 + 5*b*c^4 + c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (60 : ℝ) * a^3 * (b - a)^2 + (60 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (60 : ℝ) * a^3 * (c - b)^2 + (111 : ℝ) * a^2 * (b - a)^3 + (207 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (234 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (69 : ℝ) * a^2 * (c - b)^3 + (68 : ℝ) * a^1 * (b - a)^4 + (190 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (270 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (148 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (26 : ℝ) * a^1 * (c - b)^4 + (16 : ℝ) * (b - a)^5 + (48 : ℝ) * (b - a)^4 * (c - b)^1 + (75 : ℝ) * (b - a)^3 * (c - b)^2 + (51 : ℝ) * (b - a)^2 * (c - b)^3 + (10 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5 + 16*a^4*b + 5*a^4*c - 28*a^3*b^2 - 18*a^3*b*c + 21*a^3*c^2 + 21*a^2*b^3 + 3*a^2*b^2*c + 3*a^2*b*c^2 - 28*a^2*c^3 + 5*a*b^4 - 18*a*b^3*c + 3*a*b^2*c^2 - 18*a*b*c^3 + 16*a*c^4 + b^5 + 16*b^4*c - 28*b^3*c^2 + 21*b^2*c^3 + 5*b*c^4 + c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (60 : ℝ) * a^3 * (c - a)^2 + (60 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (60 : ℝ) * a^3 * (b - c)^2 + (111 : ℝ) * a^2 * (c - a)^3 + (126 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (153 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (69 : ℝ) * a^2 * (b - c)^3 + (68 : ℝ) * a^1 * (c - a)^4 + (82 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (108 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (94 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (26 : ℝ) * a^1 * (b - c)^4 + (16 : ℝ) * (c - a)^5 + (32 : ℝ) * (c - a)^4 * (b - c)^1 + (43 : ℝ) * (c - a)^3 * (b - c)^2 + (46 : ℝ) * (c - a)^2 * (b - c)^3 + (21 : ℝ) * (c - a)^1 * (b - c)^4 + (1 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5 + 16*a^4*b + 5*a^4*c - 28*a^3*b^2 - 18*a^3*b*c + 21*a^3*c^2 + 21*a^2*b^3 + 3*a^2*b^2*c + 3*a^2*b*c^2 - 28*a^2*c^3 + 5*a*b^4 - 18*a*b^3*c + 3*a*b^2*c^2 - 18*a*b*c^3 + 16*a*c^4 + b^5 + 16*b^4*c - 28*b^3*c^2 + 21*b^2*c^3 + 5*b*c^4 + c^5) := by
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
  have hn : 0 ≤ (a^5 + 16*a^4*b + 5*a^4*c - 28*a^3*b^2 - 18*a^3*b*c + 21*a^3*c^2 + 21*a^2*b^3 + 3*a^2*b^2*c + 3*a^2*b*c^2 - 28*a^2*c^3 + 5*a*b^4 - 18*a*b^3*c + 3*a*b^2*c^2 - 18*a*b*c^3 + 16*a*c^4 + b^5 + 16*b^4*c - 28*b^3*c^2 + 21*b^2*c^3 + 5*b*c^4 + c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + c) ^ 3 / (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + 30 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 ≥ 19) := @solution
#print axioms solution
