-- Prove2me | solution 1 for WorkbookSource.base_52437
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:58:27.679468+00:00
-- url     : https://prove2.me/submissions/b2a4e562-1cf3-4d1c-b9f9-f38200e351fe

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + 2 * b + c) + (b + c) / (b + 2 * c + a) + (c + a) / (c + 2 * a + b) ≤ (a + b + c) ^ 2 / (2 * (a * b + b * c + a * c))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5 + 5*a^4*b + 5*a^4*c + 3*a^3*b^2 + a^3*c^2 + a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 3*a^2*c^3 + 5*a*b^4 - 16*a*b^2*c^2 + 5*a*c^4 + 2*b^5 + 5*b^4*c + 3*b^3*c^2 + b^2*c^3 + 5*b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * a^3 * (b - a)^2 + (64 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (64 : ℝ) * a^3 * (c - b)^2 + (128 : ℝ) * a^2 * (b - a)^3 + (189 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (189 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (64 : ℝ) * a^2 * (c - b)^3 + (84 : ℝ) * a^1 * (b - a)^4 + (164 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (182 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (102 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (20 : ℝ) * a^1 * (c - b)^4 + (18 : ℝ) * (b - a)^5 + (44 : ℝ) * (b - a)^4 * (c - b)^1 + (56 : ℝ) * (b - a)^3 * (c - b)^2 + (41 : ℝ) * (b - a)^2 * (c - b)^3 + (15 : ℝ) * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5 + 5*a^4*b + 5*a^4*c + 3*a^3*b^2 + a^3*c^2 + a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 3*a^2*c^3 + 5*a*b^4 - 16*a*b^2*c^2 + 5*a*c^4 + 2*b^5 + 5*b^4*c + 3*b^3*c^2 + b^2*c^3 + 5*b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * a^3 * (c - a)^2 + (64 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (64 : ℝ) * a^3 * (b - c)^2 + (128 : ℝ) * a^2 * (c - a)^3 + (195 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (195 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (64 : ℝ) * a^2 * (b - c)^3 + (84 : ℝ) * a^1 * (c - a)^4 + (172 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (194 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (106 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (20 : ℝ) * a^1 * (b - c)^4 + (18 : ℝ) * (c - a)^5 + (46 : ℝ) * (c - a)^4 * (b - c)^1 + (60 : ℝ) * (c - a)^3 * (b - c)^2 + (43 : ℝ) * (c - a)^2 * (b - c)^3 + (15 : ℝ) * (c - a)^1 * (b - c)^4 + (2 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5 + 5*a^4*b + 5*a^4*c + 3*a^3*b^2 + a^3*c^2 + a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 3*a^2*c^3 + 5*a*b^4 - 16*a*b^2*c^2 + 5*a*c^4 + 2*b^5 + 5*b^4*c + 3*b^3*c^2 + b^2*c^3 + 5*b*c^4 + 2*c^5) := by
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
  have hn : 0 ≤ (2*a^5 + 5*a^4*b + 5*a^4*c + 3*a^3*b^2 + a^3*c^2 + a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 3*a^2*c^3 + 5*a*b^4 - 16*a*b^2*c^2 + 5*a*c^4 + 2*b^5 + 5*b^4*c + 3*b^3*c^2 + b^2*c^3 + 5*b*c^4 + 2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (a + 2 * b + c) + (b + c) / (b + 2 * c + a) + (c + a) / (c + 2 * a + b) ≤ (a + b + c) ^ 2 / (2 * (a * b + b * c + a * c))) := @solution
#print axioms solution
