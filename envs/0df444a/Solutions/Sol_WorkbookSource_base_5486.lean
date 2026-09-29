-- Prove2me | solution 1 for WorkbookSource.base_5486
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:39.265016+00:00
-- url     : https://prove2.me/submissions/e5f9b120-470a-44b8-adbd-d8adfcddffcc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 * (b + c) / (b^2 + b * c + c^2) + b^2 * (c + a) / (c^2 + c * a + a^2) + c^2 * (a + b) / (a^2 + a * b + b^2)) ≥ 2 / 3 * (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6*b + 3*a^6*c + a^5*b^2 + 4*a^5*b*c + a^5*c^2 - a^4*b^3 - 2*a^4*b^2*c - 2*a^4*b*c^2 - a^4*c^3 - a^3*b^4 - 4*a^3*b^3*c - 2*a^3*b^2*c^2 - 4*a^3*b*c^3 - a^3*c^4 + a^2*b^5 - 2*a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 - 2*a^2*b*c^4 + a^2*c^5 + 3*a*b^6 + 4*a*b^5*c - 2*a*b^4*c^2 - 4*a*b^3*c^3 - 2*a*b^2*c^4 + 4*a*b*c^5 + 3*a*c^6 + 3*b^6*c + b^5*c^2 - b^4*c^3 - b^3*c^4 + b^2*c^5 + 3*b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^5 * (b - a)^2 + (72 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (72 : ℝ) * a^5 * (c - b)^2 + (216 : ℝ) * a^4 * (b - a)^3 + (324 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (396 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (144 : ℝ) * a^4 * (c - b)^3 + (258 : ℝ) * a^3 * (b - a)^4 + (516 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (774 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (516 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (114 : ℝ) * a^3 * (c - b)^4 + (156 : ℝ) * a^2 * (b - a)^5 + (390 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (696 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (654 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (276 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (42 : ℝ) * a^2 * (c - b)^5 + (48 : ℝ) * a^1 * (b - a)^6 + (144 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (294 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (348 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (210 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (60 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (6 : ℝ) * a^1 * (c - b)^6 + (6 : ℝ) * (b - a)^7 + (21 : ℝ) * (b - a)^6 * (c - b)^1 + (47 : ℝ) * (b - a)^5 * (c - b)^2 + (65 : ℝ) * (b - a)^4 * (c - b)^3 + (49 : ℝ) * (b - a)^3 * (c - b)^4 + (19 : ℝ) * (b - a)^2 * (c - b)^5 + (3 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6*b + 3*a^6*c + a^5*b^2 + 4*a^5*b*c + a^5*c^2 - a^4*b^3 - 2*a^4*b^2*c - 2*a^4*b*c^2 - a^4*c^3 - a^3*b^4 - 4*a^3*b^3*c - 2*a^3*b^2*c^2 - 4*a^3*b*c^3 - a^3*c^4 + a^2*b^5 - 2*a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 - 2*a^2*b*c^4 + a^2*c^5 + 3*a*b^6 + 4*a*b^5*c - 2*a*b^4*c^2 - 4*a*b^3*c^3 - 2*a*b^2*c^4 + 4*a*b*c^5 + 3*a*c^6 + 3*b^6*c + b^5*c^2 - b^4*c^3 - b^3*c^4 + b^2*c^5 + 3*b*c^6) := by
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
  have hn : 0 ≤ (3*a^6*b + 3*a^6*c + a^5*b^2 + 4*a^5*b*c + a^5*c^2 - a^4*b^3 - 2*a^4*b^2*c - 2*a^4*b*c^2 - a^4*c^3 - a^3*b^4 - 4*a^3*b^3*c - 2*a^3*b^2*c^2 - 4*a^3*b*c^3 - a^3*c^4 + a^2*b^5 - 2*a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 - 2*a^2*b*c^4 + a^2*c^5 + 3*a*b^6 + 4*a*b^5*c - 2*a*b^4*c^2 - 4*a*b^3*c^3 - 2*a*b^2*c^4 + 4*a*b*c^5 + 3*a*c^6 + 3*b^6*c + b^5*c^2 - b^4*c^3 - b^3*c^4 + b^2*c^5 + 3*b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a^2 * (b + c) / (b^2 + b * c + c^2) + b^2 * (c + a) / (c^2 + c * a + a^2) + c^2 * (a + b) / (a^2 + a * b + b^2)) ≥ 2 / 3 * (a + b + c)) := @solution
#print axioms solution
