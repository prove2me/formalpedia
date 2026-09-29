-- Prove2me | solution 1 for WorkbookSource.base_40806
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:36.213132+00:00
-- url     : https://prove2.me/submissions/36800d33-45f0-415e-bfb0-f05830e27352

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b + b * c + c * a) * (b * c / a ^ 2 + c * a / b ^ 2 + a * b / c ^ 2) ≥ 3 * (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^4 + a^4*b^3*c - 3*a^4*b^2*c^2 + a^4*b*c^3 + a^4*c^4 + a^3*b^4*c + a^3*b*c^4 - 3*a^2*b^4*c^2 - 3*a^2*b^2*c^4 + a*b^4*c^3 + a*b^3*c^4 + b^4*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^6 * (b - a)^2 + (6 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^6 * (c - b)^2 + (30 : ℝ) * a^5 * (b - a)^3 + (45 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (27 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (6 : ℝ) * a^5 * (c - b)^3 + (61 : ℝ) * a^4 * (b - a)^4 + (122 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (78 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (17 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^4 * (c - b)^4 + (64 : ℝ) * a^3 * (b - a)^5 + (160 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (132 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (38 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (2 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (36 : ℝ) * a^2 * (b - a)^6 + (108 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (114 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (48 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (6 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (10 : ℝ) * a^1 * (b - a)^7 + (35 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (45 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (25 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (5 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (1 : ℝ) * (b - a)^8 + (4 : ℝ) * (b - a)^7 * (c - b)^1 + (6 : ℝ) * (b - a)^6 * (c - b)^2 + (4 : ℝ) * (b - a)^5 * (c - b)^3 + (1 : ℝ) * (b - a)^4 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^4 + a^4*b^3*c - 3*a^4*b^2*c^2 + a^4*b*c^3 + a^4*c^4 + a^3*b^4*c + a^3*b*c^4 - 3*a^2*b^4*c^2 - 3*a^2*b^2*c^4 + a*b^4*c^3 + a*b^3*c^4 + b^4*c^4) := by
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
  have hn : 0 ≤ (a^4*b^4 + a^4*b^3*c - 3*a^4*b^2*c^2 + a^4*b*c^3 + a^4*c^4 + a^3*b^4*c + a^3*b*c^4 - 3*a^2*b^4*c^2 - 3*a^2*b^2*c^4 + a*b^4*c^3 + a*b^3*c^4 + b^4*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b + b * c + c * a) * (b * c / a ^ 2 + c * a / b ^ 2 + a * b / c ^ 2) ≥ 3 * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
