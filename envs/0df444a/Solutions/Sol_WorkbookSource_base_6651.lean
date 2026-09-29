-- Prove2me | solution 1 for WorkbookSource.base_6651
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:19:12.12509+00:00
-- url     : https://prove2.me/submissions/99d427de-3749-41e1-ba62-406cc5a857b4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a + 2 * b * c) + b / (b + 2 * a * c) + c / (c + 2 * a * b) ≥ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b^2/9 + 2*a^4*b*c/27 + 2*a^4*c^2/9 + 4*a^3*b^3/9 + 2*a^3*b^2*c/3 + 2*a^3*b*c^2/3 + 4*a^3*c^3/9 + 2*a^2*b^4/9 + 2*a^2*b^3*c/3 - 62*a^2*b^2*c^2/9 + 2*a^2*b*c^3/3 + 2*a^2*c^4/9 + 2*a*b^4*c/27 + 2*a*b^3*c^2/3 + 2*a*b^2*c^3/3 + 2*a*b*c^4/27 + 2*b^4*c^2/9 + 4*b^3*c^3/9 + 2*b^2*c^4/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (14/3 : ℝ) * a^4 * (b - a)^2 + (14/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (14/3 : ℝ) * a^4 * (c - b)^2 + (388/27 : ℝ) * a^3 * (b - a)^3 + (194/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (142/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (116/27 : ℝ) * a^3 * (c - b)^3 + (422/27 : ℝ) * a^2 * (b - a)^4 + (844/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (208/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (202/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (14/27 : ℝ) * a^2 * (c - b)^4 + (184/27 : ℝ) * a^1 * (b - a)^5 + (460/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (44/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (134/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (14/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (8/9 : ℝ) * (b - a)^6 + (8/3 : ℝ) * (b - a)^5 * (c - b)^1 + (26/9 : ℝ) * (b - a)^4 * (c - b)^2 + (4/3 : ℝ) * (b - a)^3 * (c - b)^3 + (2/9 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b^2/9 + 2*a^4*b*c/27 + 2*a^4*c^2/9 + 4*a^3*b^3/9 + 2*a^3*b^2*c/3 + 2*a^3*b*c^2/3 + 4*a^3*c^3/9 + 2*a^2*b^4/9 + 2*a^2*b^3*c/3 - 62*a^2*b^2*c^2/9 + 2*a^2*b*c^3/3 + 2*a^2*c^4/9 + 2*a*b^4*c/27 + 2*a*b^3*c^2/3 + 2*a*b^2*c^3/3 + 2*a*b*c^4/27 + 2*b^4*c^2/9 + 4*b^3*c^3/9 + 2*b^2*c^4/9) := by
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
  have he : (-8*a^2*b^2*c^2 + 2*a^2*b^2 + 2*a^2*c^2 + 2*a*b*c + 2*b^2*c^2) = (2*a^4*b^2/9 + 2*a^4*b*c/27 + 2*a^4*c^2/9 + 4*a^3*b^3/9 + 2*a^3*b^2*c/3 + 2*a^3*b*c^2/3 + 4*a^3*c^3/9 + 2*a^2*b^4/9 + 2*a^2*b^3*c/3 - 62*a^2*b^2*c^2/9 + 2*a^2*b*c^3/3 + 2*a^2*c^4/9 + 2*a*b^4*c/27 + 2*a*b^3*c^2/3 + 2*a*b^2*c^3/3 + 2*a*b*c^4/27 + 2*b^4*c^2/9 + 4*b^3*c^3/9 + 2*b^2*c^4/9) := by
    linear_combination (-2*a^3*b^2/9 - 2*a^3*b*c/27 - 2*a^3*c^2/9 - 2*a^2*b^3/9 - 10*a^2*b^2*c/27 - 2*a^2*b^2/3 - 10*a^2*b*c^2/27 - 2*a^2*b*c/9 - 2*a^2*c^3/9 - 2*a^2*c^2/3 - 2*a*b^3*c/27 - 10*a*b^2*c^2/27 - 2*a*b^2*c/9 - 2*a*b*c^3/27 - 2*a*b*c^2/9 - 2*a*b*c/3 - 2*b^3*c^2/9 - 2*b^2*c^3/9 - 2*b^2*c^2/3) * hab
  have hn : 0 ≤ (-8*a^2*b^2*c^2 + 2*a^2*b^2 + 2*a^2*c^2 + 2*a*b*c + 2*b^2*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a / (a + 2 * b * c) + b / (b + 2 * a * c) + c / (c + 2 * a * b) ≥ 1) := @solution
#print axioms solution
