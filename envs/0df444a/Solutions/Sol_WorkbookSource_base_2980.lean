-- Prove2me | solution 1 for WorkbookSource.base_2980
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:03:19.161382+00:00
-- url     : https://prove2.me/submissions/cb13794b-c932-49b5-be65-f8fcad9d250a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 8 * b^2) / (4 * b + 5 * c) + (b^2 + 8 * c^2) / (4 * c + 5 * a) + (c^2 + 8 * a^2) / (4 * a + 5 * b) ≥ a + b + c  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (20*a^4 + 105*a^3*b + 116*a^3*c - 20*a^2*b^2 - 221*a^2*b*c - 20*a^2*c^2 + 116*a*b^3 - 221*a*b^2*c - 221*a*b*c^2 + 105*a*c^3 + 20*b^4 + 105*b^3*c - 20*b^2*c^2 + 116*b*c^3 + 20*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (522 : ℝ) * a^2 * (b - a)^2 + (522 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (522 : ℝ) * a^2 * (c - b)^2 + (743 : ℝ) * a^1 * (b - a)^3 + (1131 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (990 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (301 : ℝ) * a^1 * (c - b)^3 + (241 : ℝ) * (b - a)^4 + (493 : ℝ) * (b - a)^3 * (c - b)^1 + (448 : ℝ) * (b - a)^2 * (c - b)^2 + (196 : ℝ) * (b - a)^1 * (c - b)^3 + (20 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (20*a^4 + 105*a^3*b + 116*a^3*c - 20*a^2*b^2 - 221*a^2*b*c - 20*a^2*c^2 + 116*a*b^3 - 221*a*b^2*c - 221*a*b*c^2 + 105*a*c^3 + 20*b^4 + 105*b^3*c - 20*b^2*c^2 + 116*b*c^3 + 20*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (522 : ℝ) * a^2 * (c - a)^2 + (522 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (522 : ℝ) * a^2 * (b - c)^2 + (743 : ℝ) * a^1 * (c - a)^3 + (1098 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (957 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (301 : ℝ) * a^1 * (b - c)^3 + (241 : ℝ) * (c - a)^4 + (471 : ℝ) * (c - a)^3 * (b - c)^1 + (415 : ℝ) * (c - a)^2 * (b - c)^2 + (185 : ℝ) * (c - a)^1 * (b - c)^3 + (20 : ℝ) * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (20*a^4 + 105*a^3*b + 116*a^3*c - 20*a^2*b^2 - 221*a^2*b*c - 20*a^2*c^2 + 116*a*b^3 - 221*a*b^2*c - 221*a*b*c^2 + 105*a*c^3 + 20*b^4 + 105*b^3*c - 20*b^2*c^2 + 116*b*c^3 + 20*c^4) := by
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
  have hn : 0 ≤ (20*a^4 + 105*a^3*b + 116*a^3*c - 20*a^2*b^2 - 221*a^2*b*c - 20*a^2*c^2 + 116*a*b^3 - 221*a*b^2*c - 221*a*b*c^2 + 105*a*c^3 + 20*b^4 + 105*b^3*c - 20*b^2*c^2 + 116*b*c^3 + 20*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + 8 * b^2) / (4 * b + 5 * c) + (b^2 + 8 * c^2) / (4 * c + 5 * a) + (c^2 + 8 * a^2) / (4 * a + 5 * b) ≥ a + b + c) := @solution
#print axioms solution
