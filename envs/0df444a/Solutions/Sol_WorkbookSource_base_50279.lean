-- Prove2me | solution 1 for WorkbookSource.base_50279
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:39:52.589882+00:00
-- url     : https://prove2.me/submissions/21e745dd-0bf2-47ae-bc71-919aee6ff10e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b * c * (a + b + c) / (a ^ 4 + b ^ 4 + c ^ 4) + 12 * (a ^ 3 + b ^ 3 + c ^ 3) / ((a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2))) ≥ 5  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (7*a^7 - 5*a^6*b - 5*a^6*c - 5*a^5*b^2 + a^5*b*c - 5*a^5*c^2 + 7*a^4*b^3 - 3*a^4*b^2*c - 3*a^4*b*c^2 + 7*a^4*c^3 + 7*a^3*b^4 + 2*a^3*b^3*c + 2*a^3*b^2*c^2 + 2*a^3*b*c^3 + 7*a^3*c^4 - 5*a^2*b^5 - 3*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - 3*a^2*b*c^4 - 5*a^2*c^5 - 5*a*b^6 + a*b^5*c - 3*a*b^4*c^2 + 2*a*b^3*c^3 - 3*a*b^2*c^4 + a*b*c^5 - 5*a*c^6 + 7*b^7 - 5*b^6*c - 5*b^5*c^2 + 7*b^4*c^3 + 7*b^3*c^4 - 5*b^2*c^5 - 5*b*c^6 + 7*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^5 * (b - a)^2 + (3 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^5 * (c - b)^2 + (8 : ℝ) * a^4 * (b - a)^3 + (12 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (18 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (7 : ℝ) * a^4 * (c - b)^3 + (60 : ℝ) * a^3 * (b - a)^4 + (120 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (190 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (130 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (58 : ℝ) * a^3 * (c - b)^4 + (84 : ℝ) * a^2 * (b - a)^5 + (210 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (420 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (420 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (282 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (78 : ℝ) * a^2 * (c - b)^5 + (44 : ℝ) * a^1 * (b - a)^6 + (132 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (320 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (420 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (383 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (195 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (39 : ℝ) * a^1 * (c - b)^6 + (8 : ℝ) * (b - a)^7 + (28 : ℝ) * (b - a)^6 * (c - b)^1 + (80 : ℝ) * (b - a)^5 * (c - b)^2 + (130 : ℝ) * (b - a)^4 * (c - b)^3 + (152 : ℝ) * (b - a)^3 * (c - b)^4 + (112 : ℝ) * (b - a)^2 * (c - b)^5 + (44 : ℝ) * (b - a)^1 * (c - b)^6 + (7 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (7*a^7 - 5*a^6*b - 5*a^6*c - 5*a^5*b^2 + a^5*b*c - 5*a^5*c^2 + 7*a^4*b^3 - 3*a^4*b^2*c - 3*a^4*b*c^2 + 7*a^4*c^3 + 7*a^3*b^4 + 2*a^3*b^3*c + 2*a^3*b^2*c^2 + 2*a^3*b*c^3 + 7*a^3*c^4 - 5*a^2*b^5 - 3*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - 3*a^2*b*c^4 - 5*a^2*c^5 - 5*a*b^6 + a*b^5*c - 3*a*b^4*c^2 + 2*a*b^3*c^3 - 3*a*b^2*c^4 + a*b*c^5 - 5*a*c^6 + 7*b^7 - 5*b^6*c - 5*b^5*c^2 + 7*b^4*c^3 + 7*b^3*c^4 - 5*b^2*c^5 - 5*b*c^6 + 7*c^7) := by
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
  have hn : 0 ≤ (7*a^7 - 5*a^6*b - 5*a^6*c - 5*a^5*b^2 + a^5*b*c - 5*a^5*c^2 + 7*a^4*b^3 - 3*a^4*b^2*c - 3*a^4*b*c^2 + 7*a^4*c^3 + 7*a^3*b^4 + 2*a^3*b^3*c + 2*a^3*b^2*c^2 + 2*a^3*b*c^3 + 7*a^3*c^4 - 5*a^2*b^5 - 3*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - 3*a^2*b*c^4 - 5*a^2*c^5 - 5*a*b^6 + a*b^5*c - 3*a*b^4*c^2 + 2*a*b^3*c^3 - 3*a*b^2*c^4 + a*b*c^5 - 5*a*c^6 + 7*b^7 - 5*b^6*c - 5*b^5*c^2 + 7*b^4*c^3 + 7*b^3*c^4 - 5*b^2*c^5 - 5*b*c^6 + 7*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b * c * (a + b + c) / (a ^ 4 + b ^ 4 + c ^ 4) + 12 * (a ^ 3 + b ^ 3 + c ^ 3) / ((a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2))) ≥ 5) := @solution
#print axioms solution
