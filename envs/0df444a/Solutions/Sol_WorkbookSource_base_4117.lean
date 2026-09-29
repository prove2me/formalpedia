-- Prove2me | solution 1 for WorkbookSource.base_4117
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:11:36.901275+00:00
-- url     : https://prove2.me/submissions/3dccbb68-5f39-45f5-9367-47a43b37507b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^2 * (1 / a + 1 / b + 1 / c) + 27 * a * b * c ≥ 2 * (a + b + c)^3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b + a^5*c - a^4*b*c + 2*a^3*b^3 - 4*a^3*b^2*c - 4*a^3*b*c^2 + 2*a^3*c^3 - 4*a^2*b^3*c + 15*a^2*b^2*c^2 - 4*a^2*b*c^3 + a*b^5 - a*b^4*c - 4*a*b^3*c^2 - 4*a*b^2*c^3 - a*b*c^4 + a*c^5 + b^5*c + 2*b^3*c^3 + b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^4 * (b - a)^2 + (9 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^4 * (c - b)^2 + (24 : ℝ) * a^3 * (b - a)^3 + (36 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (36 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^3 * (c - b)^3 + (27 : ℝ) * a^2 * (b - a)^4 + (54 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (63 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (36 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (9 : ℝ) * a^2 * (c - b)^4 + (16 : ℝ) * a^1 * (b - a)^5 + (40 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (52 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (38 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (14 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (16 : ℝ) * (b - a)^4 * (c - b)^2 + (12 : ℝ) * (b - a)^3 * (c - b)^3 + (5 : ℝ) * (b - a)^2 * (c - b)^4 + (1 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b + a^5*c - a^4*b*c + 2*a^3*b^3 - 4*a^3*b^2*c - 4*a^3*b*c^2 + 2*a^3*c^3 - 4*a^2*b^3*c + 15*a^2*b^2*c^2 - 4*a^2*b*c^3 + a*b^5 - a*b^4*c - 4*a*b^3*c^2 - 4*a*b^2*c^3 - a*b*c^4 + a*c^5 + b^5*c + 2*b^3*c^3 + b*c^5) := by
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
  have hn : 0 ≤ (a^5*b + a^5*c - a^4*b*c + 2*a^3*b^3 - 4*a^3*b^2*c - 4*a^3*b*c^2 + 2*a^3*c^3 - 4*a^2*b^3*c + 15*a^2*b^2*c^2 - 4*a^2*b*c^3 + a*b^5 - a*b^4*c - 4*a*b^3*c^2 - 4*a*b^2*c^3 - a*b*c^4 + a*c^5 + b^5*c + 2*b^3*c^3 + b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2)^2 * (1 / a + 1 / b + 1 / c) + 27 * a * b * c ≥ 2 * (a + b + c)^3) := @solution
#print axioms solution
