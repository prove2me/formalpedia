-- Prove2me | solution 1 for WorkbookSource.base_16260
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:03:46.130454+00:00
-- url     : https://prove2.me/submissions/42fc22f9-996e-4c6c-941a-a7252e31176c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3) / (a^2 + b^2) + (b^3 + c^3) / (b^2 + c^2) + (c^3 + a^3) / (c^2 + a^2) ≥ a + b + c  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b^2 + a^5*c^2 - a^4*b^2*c - a^4*b*c^2 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^5*c^2 + b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^5 * (b - a)^2 + (8 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^5 * (c - b)^2 + (28 : ℝ) * a^4 * (b - a)^3 + (42 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (38 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^4 * (c - b)^3 + (40 : ℝ) * a^3 * (b - a)^4 + (80 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (80 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (40 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^3 * (c - b)^4 + (30 : ℝ) * a^2 * (b - a)^5 + (75 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (86 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (54 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (17 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^2 * (c - b)^5 + (12 : ℝ) * a^1 * (b - a)^6 + (36 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (48 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (36 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (14 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (b - a)^7 + (7 : ℝ) * (b - a)^6 * (c - b)^1 + (11 : ℝ) * (b - a)^5 * (c - b)^2 + (10 : ℝ) * (b - a)^4 * (c - b)^3 + (5 : ℝ) * (b - a)^3 * (c - b)^4 + (1 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b^2 + a^5*c^2 - a^4*b^2*c - a^4*b*c^2 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^5*c^2 + b^2*c^5) := by
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
  have hn : 0 ≤ (a^5*b^2 + a^5*c^2 - a^4*b^2*c - a^4*b*c^2 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^5*c^2 + b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3) / (a^2 + b^2) + (b^3 + c^3) / (b^2 + c^2) + (c^3 + a^3) / (c^2 + a^2) ≥ a + b + c) := @solution
#print axioms solution
