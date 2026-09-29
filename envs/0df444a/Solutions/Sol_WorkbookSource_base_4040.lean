-- Prove2me | solution 1 for WorkbookSource.base_4040
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:11:36.133097+00:00
-- url     : https://prove2.me/submissions/01322ece-312a-43e7-a57b-56f04a47f73e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (b^2 + c^2) + b^3 / (c^2 + a^2) + c^3 / (a^2 + b^2)) ≥ (a + b + c) / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^7 + a^5*b^2 + a^5*c^2 - a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 - a^3*c^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + 2*b^7 + b^5*c^2 - b^4*c^3 - b^3*c^4 + b^2*c^5 + 2*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * a^5 * (b - a)^2 + (32 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (32 : ℝ) * a^5 * (c - b)^2 + (88 : ℝ) * a^4 * (b - a)^3 + (132 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (188 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (72 : ℝ) * a^4 * (c - b)^3 + (108 : ℝ) * a^3 * (b - a)^4 + (216 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (404 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (296 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (76 : ℝ) * a^3 * (c - b)^4 + (72 : ℝ) * a^2 * (b - a)^5 + (180 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (416 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (444 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (224 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (44 : ℝ) * a^2 * (c - b)^5 + (26 : ℝ) * a^1 * (b - a)^6 + (78 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (213 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (296 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (221 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (86 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (14 : ℝ) * a^1 * (c - b)^6 + (4 : ℝ) * (b - a)^7 + (14 : ℝ) * (b - a)^6 * (c - b)^1 + (44 : ℝ) * (b - a)^5 * (c - b)^2 + (75 : ℝ) * (b - a)^4 * (c - b)^3 + (74 : ℝ) * (b - a)^3 * (c - b)^4 + (43 : ℝ) * (b - a)^2 * (c - b)^5 + (14 : ℝ) * (b - a)^1 * (c - b)^6 + (2 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^7 + a^5*b^2 + a^5*c^2 - a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 - a^3*c^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + 2*b^7 + b^5*c^2 - b^4*c^3 - b^3*c^4 + b^2*c^5 + 2*c^7) := by
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
  have hn : 0 ≤ (2*a^7 + a^5*b^2 + a^5*c^2 - a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 - a^3*c^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + 2*b^7 + b^5*c^2 - b^4*c^3 - b^3*c^4 + b^2*c^5 + 2*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 / (b^2 + c^2) + b^3 / (c^2 + a^2) + c^3 / (a^2 + b^2)) ≥ (a + b + c) / 2) := @solution
#print axioms solution
