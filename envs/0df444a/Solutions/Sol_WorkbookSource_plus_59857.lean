-- Prove2me | solution 1 for WorkbookSource.plus_59857
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:41:53.551649+00:00
-- url     : https://prove2.me/submissions/82dd0211-de53-400f-9987-ed84f2b4aac0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a^4 + b^4 + c^4) * (a + b) * (b + c) * (c + a) ≥ (a + b + c) * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b + a^6*c + 2*a^5*b*c - a^4*b^3 - a^4*c^3 - a^3*b^4 - 2*a^3*b^2*c^2 - a^3*c^4 - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 + a*b^6 + 2*a*b^5*c + 2*a*b*c^5 + a*c^6 + b^6*c - b^4*c^3 - b^3*c^4 + b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (22 : ℝ) * a^5 * (b - a)^2 + (22 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (22 : ℝ) * a^5 * (c - b)^2 + (62 : ℝ) * a^4 * (b - a)^3 + (93 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (127 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (48 : ℝ) * a^4 * (c - b)^3 + (66 : ℝ) * a^3 * (b - a)^4 + (132 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (238 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (172 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (38 : ℝ) * a^3 * (c - b)^4 + (32 : ℝ) * a^2 * (b - a)^5 + (80 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (192 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (208 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (92 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (14 : ℝ) * a^2 * (c - b)^5 + (6 : ℝ) * a^1 * (b - a)^6 + (18 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (65 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (100 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (67 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (20 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^1 * (c - b)^6 + (6 : ℝ) * (b - a)^5 * (c - b)^2 + (15 : ℝ) * (b - a)^4 * (c - b)^3 + (14 : ℝ) * (b - a)^3 * (c - b)^4 + (6 : ℝ) * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b + a^6*c + 2*a^5*b*c - a^4*b^3 - a^4*c^3 - a^3*b^4 - 2*a^3*b^2*c^2 - a^3*c^4 - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 + a*b^6 + 2*a*b^5*c + 2*a*b*c^5 + a*c^6 + b^6*c - b^4*c^3 - b^3*c^4 + b*c^6) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a^4 + b^4 + c^4) * (a + b) * (b + c) * (c + a) ≥ (a + b + c) * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)) := @solution
#print axioms solution
