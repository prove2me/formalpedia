-- Prove2me | solution 1 for WorkbookSource.plus_77676
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:30.172866+00:00
-- url     : https://prove2.me/submissions/8f0223d4-de95-4ad7-be7a-21e68623e190

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 + b^4 + c^4 ≥ a^3 * (b^2 + c^2) / (b + c) + b^3 * (c^2 + a^2) / (c + a) + c^3 * (a^2 + b^2) / (a + b)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b + a^6*c + 2*a^5*b*c - a^4*b^3 - a^4*c^3 - a^3*b^4 - 2*a^3*b^3*c - 2*a^3*b*c^3 - a^3*c^4 + a*b^6 + 2*a*b^5*c - 2*a*b^3*c^3 + 2*a*b*c^5 + a*c^6 + b^6*c - b^4*c^3 - b^3*c^4 + b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^5 * (b - a)^2 + (20 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (20 : ℝ) * a^5 * (c - b)^2 + (54 : ℝ) * a^4 * (b - a)^3 + (81 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (119 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (46 : ℝ) * a^4 * (c - b)^3 + (54 : ℝ) * a^3 * (b - a)^4 + (108 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (222 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (168 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (38 : ℝ) * a^3 * (c - b)^4 + (24 : ℝ) * a^2 * (b - a)^5 + (60 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (176 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (204 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (92 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (14 : ℝ) * a^2 * (c - b)^5 + (4 : ℝ) * a^1 * (b - a)^6 + (12 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (59 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (98 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (67 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (20 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^1 * (c - b)^6 + (6 : ℝ) * (b - a)^5 * (c - b)^2 + (15 : ℝ) * (b - a)^4 * (c - b)^3 + (14 : ℝ) * (b - a)^3 * (c - b)^4 + (6 : ℝ) * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b + a^6*c + 2*a^5*b*c - a^4*b^3 - a^4*c^3 - a^3*b^4 - 2*a^3*b^3*c - 2*a^3*b*c^3 - a^3*c^4 + a*b^6 + 2*a*b^5*c - 2*a*b^3*c^3 + 2*a*b*c^5 + a*c^6 + b^6*c - b^4*c^3 - b^3*c^4 + b*c^6) := by
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
  have hn : 0 ≤ (a^6*b + a^6*c + 2*a^5*b*c - a^4*b^3 - a^4*c^3 - a^3*b^4 - 2*a^3*b^3*c - 2*a^3*b*c^3 - a^3*c^4 + a*b^6 + 2*a*b^5*c - 2*a*b^3*c^3 + 2*a*b*c^5 + a*c^6 + b^6*c - b^4*c^3 - b^3*c^4 + b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^4 + b^4 + c^4 ≥ a^3 * (b^2 + c^2) / (b + c) + b^3 * (c^2 + a^2) / (c + a) + c^3 * (a^2 + b^2) / (a + b)) := @solution
#print axioms solution
