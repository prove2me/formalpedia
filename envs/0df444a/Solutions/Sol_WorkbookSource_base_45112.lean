-- Prove2me | solution 1 for WorkbookSource.base_45112
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:15:13.208912+00:00
-- url     : https://prove2.me/submissions/35d65972-885f-4145-a614-f224196b9fcc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 4 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 ≥ 3 * (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) ^ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 + 12*a^4*b^2 - 18*a^4*b*c + 12*a^4*c^2 - 6*a^3*b^3 - 6*a^3*c^3 + 12*a^2*b^4 - 3*a^2*b^2*c^2 + 12*a^2*c^4 - 18*a*b^4*c - 18*a*b*c^4 + b^6 + 12*b^4*c^2 - 6*b^3*c^3 + 12*b^2*c^4 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^4 * (b - a)^2 + (36 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^4 * (c - b)^2 + (112 : ℝ) * a^3 * (b - a)^3 + (168 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (120 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (32 : ℝ) * a^3 * (c - b)^3 + (141 : ℝ) * a^2 * (b - a)^4 + (282 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (231 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (90 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (21 : ℝ) * a^2 * (c - b)^4 + (84 : ℝ) * a^1 * (b - a)^5 + (210 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (216 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (114 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (36 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^1 * (c - b)^5 + (20 : ℝ) * (b - a)^6 + (60 : ℝ) * (b - a)^5 * (c - b)^1 + (81 : ℝ) * (b - a)^4 * (c - b)^2 + (62 : ℝ) * (b - a)^3 * (c - b)^3 + (27 : ℝ) * (b - a)^2 * (c - b)^4 + (6 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 + 12*a^4*b^2 - 18*a^4*b*c + 12*a^4*c^2 - 6*a^3*b^3 - 6*a^3*c^3 + 12*a^2*b^4 - 3*a^2*b^2*c^2 + 12*a^2*c^4 - 18*a*b^4*c - 18*a*b*c^4 + b^6 + 12*b^4*c^2 - 6*b^3*c^3 + 12*b^2*c^4 + c^6) := by
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
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), 4 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 ≥ 3 * (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) ^ 2) := @solution
#print axioms solution
