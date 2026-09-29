-- Prove2me | solution 1 for WorkbookSource.base_48525
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:27:03.384343+00:00
-- url     : https://prove2.me/submissions/f66a8bb9-ae9b-478e-a963-98292050c3a8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 / (b + c) + b^5 / (c + a) + c^5 / (a + b)) ≥ (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^7 + 2*a^6*b + 2*a^6*c + 2*a^5*b*c - a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 - 2*a^3*b^3*c - 2*a^3*b^2*c^2 - 2*a^3*b*c^3 - a^3*c^4 - a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 - a^2*b*c^4 + 2*a*b^6 + 2*a*b^5*c - a*b^4*c^2 - 2*a*b^3*c^3 - a*b^2*c^4 + 2*a*b*c^5 + 2*a*c^6 + 2*b^7 + 2*b^6*c - b^4*c^3 - b^3*c^4 + 2*b*c^6 + 2*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (68 : ℝ) * a^5 * (b - a)^2 + (68 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (68 : ℝ) * a^5 * (c - b)^2 + (194 : ℝ) * a^4 * (b - a)^3 + (291 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (389 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (146 : ℝ) * a^4 * (c - b)^3 + (232 : ℝ) * a^3 * (b - a)^4 + (464 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (796 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (564 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (136 : ℝ) * a^3 * (c - b)^4 + (144 : ℝ) * a^2 * (b - a)^5 + (360 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (764 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (786 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (374 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (68 : ℝ) * a^2 * (c - b)^5 + (46 : ℝ) * a^1 * (b - a)^6 + (138 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (352 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (474 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (336 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (122 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (18 : ℝ) * a^1 * (c - b)^6 + (6 : ℝ) * (b - a)^7 + (21 : ℝ) * (b - a)^6 * (c - b)^1 + (63 : ℝ) * (b - a)^5 * (c - b)^2 + (105 : ℝ) * (b - a)^4 * (c - b)^3 + (99 : ℝ) * (b - a)^3 * (c - b)^4 + (54 : ℝ) * (b - a)^2 * (c - b)^5 + (16 : ℝ) * (b - a)^1 * (c - b)^6 + (2 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^7 + 2*a^6*b + 2*a^6*c + 2*a^5*b*c - a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 - 2*a^3*b^3*c - 2*a^3*b^2*c^2 - 2*a^3*b*c^3 - a^3*c^4 - a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 - a^2*b*c^4 + 2*a*b^6 + 2*a*b^5*c - a*b^4*c^2 - 2*a*b^3*c^3 - a*b^2*c^4 + 2*a*b*c^5 + 2*a*c^6 + 2*b^7 + 2*b^6*c - b^4*c^3 - b^3*c^4 + 2*b*c^6 + 2*c^7) := by
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
  have hn : 0 ≤ (2*a^7 + 2*a^6*b + 2*a^6*c + 2*a^5*b*c - a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 - 2*a^3*b^3*c - 2*a^3*b^2*c^2 - 2*a^3*b*c^3 - a^3*c^4 - a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 - a^2*b*c^4 + 2*a*b^6 + 2*a*b^5*c - a*b^4*c^2 - 2*a*b^3*c^3 - a*b^2*c^4 + 2*a*b*c^5 + 2*a*c^6 + 2*b^7 + 2*b^6*c - b^4*c^3 - b^3*c^4 + 2*b*c^6 + 2*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^5 / (b + c) + b^5 / (c + a) + c^5 / (a + b)) ≥ (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) / 2) := @solution
#print axioms solution
