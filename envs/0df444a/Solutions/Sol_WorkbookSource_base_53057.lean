-- Prove2me | solution 1 for WorkbookSource.base_53057
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:03:57.91184+00:00
-- url     : https://prove2.me/submissions/3ed0a716-9ea1-4089-8ab2-5ce487fd8bb6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * a^2 + (b + c)^2) + b^2 / (2 * b^2 + (c + a)^2) + c^2 / (2 * c^2 + (a + b)^2)) ≥ 1 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^4*b^2 - 2*a^4*b*c + 3*a^4*c^2 + 6*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 + 6*a^3*c^3 + 3*a^2*b^4 - 6*a^2*b^3*c + 6*a^2*b^2*c^2 - 6*a^2*b*c^3 + 3*a^2*c^4 - 2*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 - 2*a*b*c^4 + 3*b^4*c^2 + 6*b^3*c^3 + 3*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^4 * (b - a)^2 + (24 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^4 * (c - b)^2 + (80 : ℝ) * a^3 * (b - a)^3 + (120 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (72 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (16 : ℝ) * a^3 * (c - b)^3 + (100 : ℝ) * a^2 * (b - a)^4 + (200 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (132 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (32 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (56 : ℝ) * a^1 * (b - a)^5 + (140 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (120 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (40 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * (b - a)^6 + (36 : ℝ) * (b - a)^5 * (c - b)^1 + (39 : ℝ) * (b - a)^4 * (c - b)^2 + (18 : ℝ) * (b - a)^3 * (c - b)^3 + (3 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^4*b^2 - 2*a^4*b*c + 3*a^4*c^2 + 6*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 + 6*a^3*c^3 + 3*a^2*b^4 - 6*a^2*b^3*c + 6*a^2*b^2*c^2 - 6*a^2*b*c^3 + 3*a^2*c^4 - 2*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 - 2*a*b*c^4 + 3*b^4*c^2 + 6*b^3*c^3 + 3*b^2*c^4) := by
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
  have hn : 0 ≤ (3*a^4*b^2 - 2*a^4*b*c + 3*a^4*c^2 + 6*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 + 6*a^3*c^3 + 3*a^2*b^4 - 6*a^2*b^3*c + 6*a^2*b^2*c^2 - 6*a^2*b*c^3 + 3*a^2*c^4 - 2*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 - 2*a*b*c^4 + 3*b^4*c^2 + 6*b^3*c^3 + 3*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (2 * a^2 + (b + c)^2) + b^2 / (2 * b^2 + (c + a)^2) + c^2 / (2 * c^2 + (a + b)^2)) ≥ 1 / 2) := @solution
#print axioms solution
