-- Prove2me | solution 1 for WorkbookSource.base_40599
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:18.386316+00:00
-- url     : https://prove2.me/submissions/43676418-47f0-4648-9fce-5bc30d22495e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c) ≥ 36 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 + 3*a^5*b + 3*a^5*c + 3*a^4*b^2 - 29*a^4*b*c + 3*a^4*c^2 + 2*a^3*b^3 + 6*a^3*b^2*c + 6*a^3*b*c^2 + 2*a^3*c^3 + 3*a^2*b^4 + 6*a^2*b^3*c + 6*a^2*b^2*c^2 + 6*a^2*b*c^3 + 3*a^2*c^4 + 3*a*b^5 - 29*a*b^4*c + 6*a*b^3*c^2 + 6*a*b^2*c^3 - 29*a*b*c^4 + 3*a*c^5 + b^6 + 3*b^5*c + 3*b^4*c^2 + 2*b^3*c^3 + 3*b^2*c^4 + 3*b*c^5 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^4 * (b - a)^2 + (9 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^4 * (c - b)^2 + (32 : ℝ) * a^3 * (b - a)^3 + (48 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (24 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^3 * (c - b)^3 + (64 : ℝ) * a^2 * (b - a)^4 + (128 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (114 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (50 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (22 : ℝ) * a^2 * (c - b)^4 + (56 : ℝ) * a^1 * (b - a)^5 + (140 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (168 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (112 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (52 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^6 + (48 : ℝ) * (b - a)^5 * (c - b)^1 + (72 : ℝ) * (b - a)^4 * (c - b)^2 + (64 : ℝ) * (b - a)^3 * (c - b)^3 + (33 : ℝ) * (b - a)^2 * (c - b)^4 + (9 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 + 3*a^5*b + 3*a^5*c + 3*a^4*b^2 - 29*a^4*b*c + 3*a^4*c^2 + 2*a^3*b^3 + 6*a^3*b^2*c + 6*a^3*b*c^2 + 2*a^3*c^3 + 3*a^2*b^4 + 6*a^2*b^3*c + 6*a^2*b^2*c^2 + 6*a^2*b*c^3 + 3*a^2*c^4 + 3*a*b^5 - 29*a*b^4*c + 6*a*b^3*c^2 + 6*a*b^2*c^3 - 29*a*b*c^4 + 3*a*c^5 + b^6 + 3*b^5*c + 3*b^4*c^2 + 2*b^3*c^3 + 3*b^2*c^4 + 3*b*c^5 + c^6) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + c) ^ 3 * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c) ≥ 36 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3)) := @solution
#print axioms solution
