-- Prove2me | solution 1 for WorkbookSource.base_4944
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:15:19.106814+00:00
-- url     : https://prove2.me/submissions/7329d3b9-18ef-4030-9013-72dafc50649d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a ^ 2 + b ^ 2) + (b + c) / (b ^ 2 + c ^ 2) + (c + a) / (c ^ 2 + a ^ 2) ≤ 1 / a + 1 / b + 1 / c  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b^3 + a^5*c^3 - a^4*b^3*c - a^4*b*c^3 + a^3*b^5 - a^3*b^4*c - a^3*b*c^4 + a^3*c^5 - a*b^4*c^3 - a*b^3*c^4 + b^5*c^3 + b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^6 * (b - a)^2 + (8 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^6 * (c - b)^2 + (36 : ℝ) * a^5 * (b - a)^3 + (54 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (42 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^5 * (c - b)^3 + (68 : ℝ) * a^4 * (b - a)^4 + (136 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (114 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (46 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^4 * (c - b)^4 + (70 : ℝ) * a^3 * (b - a)^5 + (175 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (174 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (86 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (21 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^3 * (c - b)^5 + (42 : ℝ) * a^2 * (b - a)^6 + (126 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (150 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (90 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (27 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (14 : ℝ) * a^1 * (b - a)^7 + (49 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (69 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (50 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (19 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * (b - a)^8 + (8 : ℝ) * (b - a)^7 * (c - b)^1 + (13 : ℝ) * (b - a)^6 * (c - b)^2 + (11 : ℝ) * (b - a)^5 * (c - b)^3 + (5 : ℝ) * (b - a)^4 * (c - b)^4 + (1 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b^3 + a^5*c^3 - a^4*b^3*c - a^4*b*c^3 + a^3*b^5 - a^3*b^4*c - a^3*b*c^4 + a^3*c^5 - a*b^4*c^3 - a*b^3*c^4 + b^5*c^3 + b^3*c^5) := by
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
  have hn : 0 ≤ (a^5*b^3 + a^5*c^3 - a^4*b^3*c - a^4*b*c^3 + a^3*b^5 - a^3*b^4*c - a^3*b*c^4 + a^3*c^5 - a*b^4*c^3 - a*b^3*c^4 + b^5*c^3 + b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (a ^ 2 + b ^ 2) + (b + c) / (b ^ 2 + c ^ 2) + (c + a) / (c ^ 2 + a ^ 2) ≤ 1 / a + 1 / b + 1 / c) := @solution
#print axioms solution
