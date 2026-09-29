-- Prove2me | solution 1 for WorkbookSource.base_17138
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:07:48.36204+00:00
-- url     : https://prove2.me/submissions/808a9068-fe87-4094-84fb-523d841db978

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b * c) / (b^2 + c^2) + (b^2 + c * a) / (c^2 + a^2) + (c^2 + a * b) / (a^2 + b^2) ≥ 5 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6 - 3*a^4*b^2 + 2*a^4*b*c - 3*a^4*c^2 + 2*a^3*b^3 + 2*a^3*b^2*c + 2*a^3*b*c^2 + 2*a^3*c^3 - 3*a^2*b^4 + 2*a^2*b^3*c - 4*a^2*b^2*c^2 + 2*a^2*b*c^3 - 3*a^2*c^4 + 2*a*b^4*c + 2*a*b^3*c^2 + 2*a*b^2*c^3 + 2*a*b*c^4 + 2*b^6 - 3*b^4*c^2 + 2*b^3*c^3 - 3*b^2*c^4 + 2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^6 + (32 : ℝ) * a^5 * (b - a)^1 + (16 : ℝ) * a^5 * (c - b)^1 + (64 : ℝ) * a^4 * (b - a)^2 + (64 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^4 * (c - b)^2 + (64 : ℝ) * a^3 * (b - a)^3 + (96 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (96 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (32 : ℝ) * a^3 * (c - b)^3 + (34 : ℝ) * a^2 * (b - a)^4 + (68 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (134 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (100 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (26 : ℝ) * a^2 * (c - b)^4 + (8 : ℝ) * a^1 * (b - a)^5 + (20 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (80 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (100 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (56 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * a^1 * (c - b)^5 + (15 : ℝ) * (b - a)^4 * (c - b)^2 + (30 : ℝ) * (b - a)^3 * (c - b)^3 + (27 : ℝ) * (b - a)^2 * (c - b)^4 + (12 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6 - 3*a^4*b^2 + 2*a^4*b*c - 3*a^4*c^2 + 2*a^3*b^3 + 2*a^3*b^2*c + 2*a^3*b*c^2 + 2*a^3*c^3 - 3*a^2*b^4 + 2*a^2*b^3*c - 4*a^2*b^2*c^2 + 2*a^2*b*c^3 - 3*a^2*c^4 + 2*a*b^4*c + 2*a*b^3*c^2 + 2*a*b^2*c^3 + 2*a*b*c^4 + 2*b^6 - 3*b^4*c^2 + 2*b^3*c^3 - 3*b^2*c^4 + 2*c^6) := by
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
  have hn : 0 ≤ (2*a^6 - 3*a^4*b^2 + 2*a^4*b*c - 3*a^4*c^2 + 2*a^3*b^3 + 2*a^3*b^2*c + 2*a^3*b*c^2 + 2*a^3*c^3 - 3*a^2*b^4 + 2*a^2*b^3*c - 4*a^2*b^2*c^2 + 2*a^2*b*c^3 - 3*a^2*c^4 + 2*a*b^4*c + 2*a*b^3*c^2 + 2*a*b^2*c^3 + 2*a*b*c^4 + 2*b^6 - 3*b^4*c^2 + 2*b^3*c^3 - 3*b^2*c^4 + 2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b * c) / (b^2 + c^2) + (b^2 + c * a) / (c^2 + a^2) + (c^2 + a * b) / (a^2 + b^2) ≥ 5 / 2) := @solution
#print axioms solution
