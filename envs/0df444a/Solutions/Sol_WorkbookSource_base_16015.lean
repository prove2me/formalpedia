-- Prove2me | solution 1 for WorkbookSource.base_16015
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:03:44.336792+00:00
-- url     : https://prove2.me/submissions/37ab44ab-8dc5-4989-8a23-f17d67a6ab1d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b - 3 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) + (c + a - 3 * b) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (b + c - 3 * a) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) ≥ 1 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (24*a^6 + 12*a^5*b + 12*a^5*c + 33*a^4*b^2 + 10*a^4*b*c + 33*a^4*c^2 + 90*a^3*b^3 - 138*a^3*b^2*c - 138*a^3*b*c^2 + 90*a^3*c^3 + 33*a^2*b^4 - 138*a^2*b^3*c + 186*a^2*b^2*c^2 - 138*a^2*b*c^3 + 33*a^2*c^4 + 12*a*b^5 + 10*a*b^4*c - 138*a*b^3*c^2 - 138*a*b^2*c^3 + 10*a*b*c^4 + 12*a*c^5 + 24*b^6 + 12*b^5*c + 33*b^4*c^2 + 90*b^3*c^3 + 33*b^2*c^4 + 12*b*c^5 + 24*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (744 : ℝ) * a^4 * (b - a)^2 + (744 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (744 : ℝ) * a^4 * (c - b)^2 + (2048 : ℝ) * a^3 * (b - a)^3 + (3072 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (2880 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (928 : ℝ) * a^3 * (c - b)^3 + (2236 : ℝ) * a^2 * (b - a)^4 + (4472 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (4740 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (2504 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (556 : ℝ) * a^2 * (c - b)^4 + (1136 : ℝ) * a^1 * (b - a)^5 + (2840 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (3552 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (2488 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (976 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (168 : ℝ) * a^1 * (c - b)^5 + (228 : ℝ) * (b - a)^6 + (684 : ℝ) * (b - a)^5 * (c - b)^1 + (981 : ℝ) * (b - a)^4 * (c - b)^2 + (822 : ℝ) * (b - a)^3 * (c - b)^3 + (453 : ℝ) * (b - a)^2 * (c - b)^4 + (156 : ℝ) * (b - a)^1 * (c - b)^5 + (24 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (24*a^6 + 12*a^5*b + 12*a^5*c + 33*a^4*b^2 + 10*a^4*b*c + 33*a^4*c^2 + 90*a^3*b^3 - 138*a^3*b^2*c - 138*a^3*b*c^2 + 90*a^3*c^3 + 33*a^2*b^4 - 138*a^2*b^3*c + 186*a^2*b^2*c^2 - 138*a^2*b*c^3 + 33*a^2*c^4 + 12*a*b^5 + 10*a*b^4*c - 138*a*b^3*c^2 - 138*a*b^2*c^3 + 10*a*b*c^4 + 12*a*c^5 + 24*b^6 + 12*b^5*c + 33*b^4*c^2 + 90*b^3*c^3 + 33*b^2*c^4 + 12*b*c^5 + 24*c^6) := by
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
  have hn : 0 ≤ (24*a^6 + 12*a^5*b + 12*a^5*c + 33*a^4*b^2 + 10*a^4*b*c + 33*a^4*c^2 + 90*a^3*b^3 - 138*a^3*b^2*c - 138*a^3*b*c^2 + 90*a^3*c^3 + 33*a^2*b^4 - 138*a^2*b^3*c + 186*a^2*b^2*c^2 - 138*a^2*b*c^3 + 33*a^2*c^4 + 12*a*b^5 + 10*a*b^4*c - 138*a*b^3*c^2 - 138*a*b^2*c^3 + 10*a*b*c^4 + 12*a*c^5 + 24*b^6 + 12*b^5*c + 33*b^4*c^2 + 90*b^3*c^3 + 33*b^2*c^4 + 12*b*c^5 + 24*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a + b - 3 * c) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) + (c + a - 3 * b) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (b + c - 3 * a) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) ≥ 1 / 2) := @solution
#print axioms solution
