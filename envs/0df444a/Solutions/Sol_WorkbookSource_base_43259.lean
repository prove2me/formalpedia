-- Prove2me | solution 1 for WorkbookSource.base_43259
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:11.227491+00:00
-- url     : https://prove2.me/submissions/cf2008a5-04cd-44fb-8899-b19fd46bb542

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * (a + b + c) ^ 2 / (a * b + b * c + a * c) + 27 * (a + b) * (b + c) * (a + c) / (a + b + c) ^ 3 ≥ 32  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^5 + 8*a^4*b + 8*a^4*c + 11*a^3*b^2 - 10*a^3*b*c + 11*a^3*c^2 + 11*a^2*b^3 - 36*a^2*b^2*c - 36*a^2*b*c^2 + 11*a^2*c^3 + 8*a*b^4 - 10*a*b^3*c - 36*a*b^2*c^2 - 10*a*b*c^3 + 8*a*c^4 + 8*b^5 + 8*b^4*c + 11*b^3*c^2 + 11*b^2*c^3 + 8*b*c^4 + 8*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (162 : ℝ) * a^3 * (b - a)^2 + (162 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (162 : ℝ) * a^3 * (c - b)^2 + (330 : ℝ) * a^2 * (b - a)^3 + (495 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (477 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (156 : ℝ) * a^2 * (c - b)^3 + (230 : ℝ) * a^1 * (b - a)^4 + (460 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (498 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (268 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (56 : ℝ) * a^1 * (c - b)^4 + (54 : ℝ) * (b - a)^5 + (135 : ℝ) * (b - a)^4 * (c - b)^1 + (172 : ℝ) * (b - a)^3 * (c - b)^2 + (123 : ℝ) * (b - a)^2 * (c - b)^3 + (48 : ℝ) * (b - a)^1 * (c - b)^4 + (8 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^5 + 8*a^4*b + 8*a^4*c + 11*a^3*b^2 - 10*a^3*b*c + 11*a^3*c^2 + 11*a^2*b^3 - 36*a^2*b^2*c - 36*a^2*b*c^2 + 11*a^2*c^3 + 8*a*b^4 - 10*a*b^3*c - 36*a*b^2*c^2 - 10*a*b*c^3 + 8*a*c^4 + 8*b^5 + 8*b^4*c + 11*b^3*c^2 + 11*b^2*c^3 + 8*b*c^4 + 8*c^5) := by
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
  have hn : 0 ≤ (8*a^5 + 8*a^4*b + 8*a^4*c + 11*a^3*b^2 - 10*a^3*b*c + 11*a^3*c^2 + 11*a^2*b^3 - 36*a^2*b^2*c - 36*a^2*b*c^2 + 11*a^2*c^3 + 8*a*b^4 - 10*a*b^3*c - 36*a*b^2*c^2 - 10*a*b*c^3 + 8*a*c^4 + 8*b^5 + 8*b^4*c + 11*b^3*c^2 + 11*b^2*c^3 + 8*b*c^4 + 8*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 8 * (a + b + c) ^ 2 / (a * b + b * c + a * c) + 27 * (a + b) * (b + c) * (a + c) / (a + b + c) ^ 3 ≥ 32) := @solution
#print axioms solution
