-- Prove2me | solution 1 for WorkbookSource.plus_13160
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:40.321059+00:00
-- url     : https://prove2.me/submissions/18d38eeb-47fe-48ea-9432-45fb0e5f6296

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 / b + b^2 / c + c^2 / a) * (a^2 / c + b^2 / a + c^2 / b) ≥ 9   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b*c + a^4*b^4 - a^4*b^2*c^2 + a^4*c^4 - a^3*b^3*c^2 - a^3*b^2*c^3 - a^2*b^4*c^2 - a^2*b^3*c^3 - a^2*b^2*c^4 + a*b^6*c + a*b*c^6 + b^4*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^6 * (b - a)^2 + (12 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^6 * (c - b)^2 + (50 : ℝ) * a^5 * (b - a)^3 + (75 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (69 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (22 : ℝ) * a^5 * (c - b)^3 + (86 : ℝ) * a^4 * (b - a)^4 + (172 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (173 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (87 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (16 : ℝ) * a^4 * (c - b)^4 + (78 : ℝ) * a^3 * (b - a)^5 + (195 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (226 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (144 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (47 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^3 * (c - b)^5 + (39 : ℝ) * a^2 * (b - a)^6 + (117 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (155 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (115 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (50 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (12 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^2 * (c - b)^6 + (10 : ℝ) * a^1 * (b - a)^7 + (35 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (51 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (40 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (19 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (1 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (b - a)^8 + (4 : ℝ) * (b - a)^7 * (c - b)^1 + (6 : ℝ) * (b - a)^6 * (c - b)^2 + (4 : ℝ) * (b - a)^5 * (c - b)^3 + (1 : ℝ) * (b - a)^4 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b*c + a^4*b^4 - a^4*b^2*c^2 + a^4*c^4 - a^3*b^3*c^2 - a^3*b^2*c^3 - a^2*b^4*c^2 - a^2*b^3*c^3 - a^2*b^2*c^4 + a*b^6*c + a*b*c^6 + b^4*c^4) := by
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
  have he : (a^6*b*c + a^4*b^4 + a^4*c^4 + a^3*b^3*c^2 + a^3*b^2*c^3 + a^2*b^3*c^3 - 9*a^2*b^2*c^2 + a*b^6*c + a*b*c^6 + b^4*c^4) = (a^6*b*c + a^4*b^4 - a^4*b^2*c^2 + a^4*c^4 - a^3*b^3*c^2 - a^3*b^2*c^3 - a^2*b^4*c^2 - a^2*b^3*c^3 - a^2*b^2*c^4 + a*b^6*c + a*b*c^6 + b^4*c^4) := by
    linear_combination (a^3*b^2*c^2 + a^2*b^3*c^2 + a^2*b^2*c^3 + 3*a^2*b^2*c^2) * hab
  have hn : 0 ≤ (a^6*b*c + a^4*b^4 + a^4*c^4 + a^3*b^3*c^2 + a^3*b^2*c^3 + a^2*b^3*c^3 - 9*a^2*b^2*c^2 + a*b^6*c + a*b*c^6 + b^4*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a^2 / b + b^2 / c + c^2 / a) * (a^2 / c + b^2 / a + c^2 / b) ≥ 9) := @solution
#print axioms solution
