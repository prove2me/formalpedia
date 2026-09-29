-- Prove2me | solution 1 for WorkbookSource.base_50610
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:47:29.655462+00:00
-- url     : https://prove2.me/submissions/d13d5529-a18a-4086-8f71-0011d9c1c8ab

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + 7 * b + c) + (b + c) / (b + 7 * c + a) + (c + a) / (c + 7 * a + b) ≥ 2 / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (10*a^3 - 24*a^2*b + 84*a^2*c + 84*a*b^2 - 210*a*b*c - 24*a*c^2 + 10*b^3 - 24*b^2*c + 84*b*c^2 + 10*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (90 : ℝ) * a^1 * (b - a)^2 + (90 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (90 : ℝ) * a^1 * (c - b)^2 + (80 : ℝ) * (b - a)^3 + (174 : ℝ) * (b - a)^2 * (c - b)^1 + (114 : ℝ) * (b - a)^1 * (c - b)^2 + (10 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (10*a^3 - 24*a^2*b + 84*a^2*c + 84*a*b^2 - 210*a*b*c - 24*a*c^2 + 10*b^3 - 24*b^2*c + 84*b*c^2 + 10*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (90 : ℝ) * a^1 * (c - a)^2 + (90 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (90 : ℝ) * a^1 * (b - c)^2 + (80 : ℝ) * (c - a)^3 + (66 : ℝ) * (c - a)^2 * (b - c)^1 + (6 : ℝ) * (c - a)^1 * (b - c)^2 + (10 : ℝ) * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*a^3 - 24*a^2*b + 84*a^2*c + 84*a*b^2 - 210*a*b*c - 24*a*c^2 + 10*b^3 - 24*b^2*c + 84*b*c^2 + 10*c^3) := by
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
  have hn : 0 ≤ (10*a^3 - 24*a^2*b + 84*a^2*c + 84*a*b^2 - 210*a*b*c - 24*a*c^2 + 10*b^3 - 24*b^2*c + 84*b*c^2 + 10*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (a + 7 * b + c) + (b + c) / (b + 7 * c + a) + (c + a) / (c + 7 * a + b) ≥ 2 / 3) := @solution
#print axioms solution
