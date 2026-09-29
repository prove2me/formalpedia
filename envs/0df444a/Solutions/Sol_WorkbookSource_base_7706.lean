-- Prove2me | solution 1 for WorkbookSource.base_7706
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:33:30.971675+00:00
-- url     : https://prove2.me/submissions/16fcba59-94dd-41a8-a17e-aec30e79fdaf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 + b^2 + c^2 + (4 * a * b * c) / 3 ≥ 13 / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (14*a^3/27 - 4*a^2*b/9 - 4*a^2*c/9 - 4*a*b^2/9 + 10*a*b*c/9 - 4*a*c^2/9 + 14*b^3/27 - 4*b^2*c/9 - 4*b*c^2/9 + 14*c^3/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * a^1 * (b - a)^2 + (2/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (2/3 : ℝ) * a^1 * (c - b)^2 + (4/27 : ℝ) * (b - a)^3 + (2/9 : ℝ) * (b - a)^2 * (c - b)^1 + (10/9 : ℝ) * (b - a)^1 * (c - b)^2 + (14/27 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (14*a^3/27 - 4*a^2*b/9 - 4*a^2*c/9 - 4*a*b^2/9 + 10*a*b*c/9 - 4*a*c^2/9 + 14*b^3/27 - 4*b^2*c/9 - 4*b*c^2/9 + 14*c^3/27) := by
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
  have he : (3*a^2 + 4*a*b*c + 3*b^2 + 3*c^2 - 13) = (14*a^3/27 - 4*a^2*b/9 - 4*a^2*c/9 - 4*a*b^2/9 + 10*a*b*c/9 - 4*a*c^2/9 + 14*b^3/27 - 4*b^2*c/9 - 4*b*c^2/9 + 14*c^3/27) := by
    linear_combination (-14*a^2/27 + 26*a*b/27 + 26*a*c/27 + 13*a/9 - 14*b^2/27 + 26*b*c/27 + 13*b/9 - 14*c^2/27 + 13*c/9 + 13/3) * habc
  have hn : 0 ≤ (3*a^2 + 4*a*b*c + 3*b^2 + 3*c^2 - 13) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a^2 + b^2 + c^2 + (4 * a * b * c) / 3 ≥ 13 / 3) := @solution
#print axioms solution
