-- Prove2me | solution 1 for WorkbookSource.base_34797
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:51:24.619774+00:00
-- url     : https://prove2.me/submissions/503cfd73-4c0d-4554-88bb-0e8f96f9a0e5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + 2 * b) + (b + c) / (b + 2 * c) + (c + a) / (c + 2 * a) ≤ (2 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a * b + b * c + a * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4*b + 8*a^4*c + 3*a^3*b^2 + 5*a^3*b*c - 4*a^3*c^2 - 4*a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 3*a^2*c^3 + 8*a*b^4 + 5*a*b^3*c - 16*a*b^2*c^2 + 5*a*b*c^3 + 4*a*c^4 + 4*b^4*c + 3*b^3*c^2 - 4*b^2*c^3 + 8*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (51 : ℝ) * a^3 * (b - a)^2 + (51 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (51 : ℝ) * a^3 * (c - b)^2 + (101 : ℝ) * a^2 * (b - a)^3 + (153 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (156 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (52 : ℝ) * a^2 * (c - b)^3 + (61 : ℝ) * a^1 * (b - a)^4 + (124 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (140 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (77 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (12 : ℝ) * a^1 * (c - b)^4 + (11 : ℝ) * (b - a)^5 + (30 : ℝ) * (b - a)^4 * (c - b)^1 + (39 : ℝ) * (b - a)^3 * (c - b)^2 + (28 : ℝ) * (b - a)^2 * (c - b)^3 + (8 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^4*b + 8*a^4*c + 3*a^3*b^2 + 5*a^3*b*c - 4*a^3*c^2 - 4*a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 3*a^2*c^3 + 8*a*b^4 + 5*a*b^3*c - 16*a*b^2*c^2 + 5*a*b*c^3 + 4*a*c^4 + 4*b^4*c + 3*b^3*c^2 - 4*b^2*c^3 + 8*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (51 : ℝ) * a^3 * (c - a)^2 + (51 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (51 : ℝ) * a^3 * (b - c)^2 + (101 : ℝ) * a^2 * (c - a)^3 + (150 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (153 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (52 : ℝ) * a^2 * (b - c)^3 + (61 : ℝ) * a^1 * (c - a)^4 + (120 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (134 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (75 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (12 : ℝ) * a^1 * (b - c)^4 + (11 : ℝ) * (c - a)^5 + (25 : ℝ) * (c - a)^4 * (b - c)^1 + (29 : ℝ) * (c - a)^3 * (b - c)^2 + (19 : ℝ) * (c - a)^2 * (b - c)^3 + (4 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4*b + 8*a^4*c + 3*a^3*b^2 + 5*a^3*b*c - 4*a^3*c^2 - 4*a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 3*a^2*c^3 + 8*a*b^4 + 5*a*b^3*c - 16*a*b^2*c^2 + 5*a*b*c^3 + 4*a*c^4 + 4*b^4*c + 3*b^3*c^2 - 4*b^2*c^3 + 8*b*c^4) := by
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
  have hn : 0 ≤ (4*a^4*b + 8*a^4*c + 3*a^3*b^2 + 5*a^3*b*c - 4*a^3*c^2 - 4*a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 3*a^2*c^3 + 8*a*b^4 + 5*a*b^3*c - 16*a*b^2*c^2 + 5*a*b*c^3 + 4*a*c^4 + 4*b^4*c + 3*b^3*c^2 - 4*b^2*c^3 + 8*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (a + 2 * b) + (b + c) / (b + 2 * c) + (c + a) / (c + 2 * a) ≤ (2 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a * b + b * c + a * c)) := @solution
#print axioms solution
