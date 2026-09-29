-- Prove2me | solution 1 for WorkbookSource.base_18019
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:13:36.809176+00:00
-- url     : https://prove2.me/submissions/af7778be-cbae-4405-9de4-ac2c65bbb3f2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (3 * a + b) + b / (3 * b + c) + c / (3 * c + a)) ≤ 3 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^2*b + 5*a^2*c + 5*a*b^2 - 24*a*b*c + 3*a*c^2 + 3*b^2*c + 5*b*c^2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^1 * (b - a)^2 + (8 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^1 * (c - b)^2 + (8 : ℝ) * (b - a)^3 + (13 : ℝ) * (b - a)^2 * (c - b)^1 + (5 : ℝ) * (b - a)^1 * (c - b)^2 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^2*b + 5*a^2*c + 5*a*b^2 - 24*a*b*c + 3*a*c^2 + 3*b^2*c + 5*b*c^2) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^1 * (c - a)^2 + (8 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (8 : ℝ) * a^1 * (b - c)^2 + (8 : ℝ) * (c - a)^3 + (11 : ℝ) * (c - a)^2 * (b - c)^1 + (3 : ℝ) * (c - a)^1 * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^2*b + 5*a^2*c + 5*a*b^2 - 24*a*b*c + 3*a*c^2 + 3*b^2*c + 5*b*c^2) := by
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
  have hn : 0 ≤ (3*a^2*b + 5*a^2*c + 5*a*b^2 - 24*a*b*c + 3*a*c^2 + 3*b^2*c + 5*b*c^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (3 * a + b) + b / (3 * b + c) + c / (3 * c + a)) ≤ 3 / 4) := @solution
#print axioms solution
