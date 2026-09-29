-- Prove2me | solution 1 for WorkbookSource.base_50181
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:39:51.047619+00:00
-- url     : https://prove2.me/submissions/ec1b2978-2326-47f2-a3c2-4221fa71a3f6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b * c) / (a + a^2) + (b + c * a) / (b + b^2) + (c + a * b) / (c + c^2) ≥ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^3*b^3 + a^3*b^2 + a^3*c^3 + a^3*c^2 + a^2*b^3 - 3*a^2*b^2*c^2 - 2*a^2*b^2*c + a^2*b^2 - 2*a^2*b*c^2 - a^2*b*c + a^2*c^3 + a^2*c^2 - 2*a*b^2*c^2 - a*b^2*c - a*b*c^2 + b^3*c^3 + b^3*c^2 + b^2*c^3 + b^2*c^2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^4 * (b - a)^2 + (3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^4 * (c - b)^2 + (10 : ℝ) * a^3 * (b - a)^3 + (15 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (4 : ℝ) * a^3 * (b - a)^2 + (9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^3 * (c - b)^3 + (4 : ℝ) * a^3 * (c - b)^2 + (12 : ℝ) * a^2 * (b - a)^4 + (24 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (10 : ℝ) * a^2 * (b - a)^3 + (15 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (15 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (1 : ℝ) * a^2 * (b - a)^2 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (9 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (1 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^2 * (c - b)^3 + (1 : ℝ) * a^2 * (c - b)^2 + (6 : ℝ) * a^1 * (b - a)^5 + (15 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (8 : ℝ) * a^1 * (b - a)^4 + (12 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (16 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (2 : ℝ) * a^1 * (b - a)^3 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (10 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (1 : ℝ) * (b - a)^6 + (3 : ℝ) * (b - a)^5 * (c - b)^1 + (2 : ℝ) * (b - a)^5 + (3 : ℝ) * (b - a)^4 * (c - b)^2 + (5 : ℝ) * (b - a)^4 * (c - b)^1 + (1 : ℝ) * (b - a)^4 + (1 : ℝ) * (b - a)^3 * (c - b)^3 + (4 : ℝ) * (b - a)^3 * (c - b)^2 + (2 : ℝ) * (b - a)^3 * (c - b)^1 + (1 : ℝ) * (b - a)^2 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3*b^3 + a^3*b^2 + a^3*c^3 + a^3*c^2 + a^2*b^3 - 3*a^2*b^2*c^2 - 2*a^2*b^2*c + a^2*b^2 - 2*a^2*b*c^2 - a^2*b*c + a^2*c^3 + a^2*c^2 - 2*a*b^2*c^2 - a*b^2*c - a*b*c^2 + b^3*c^3 + b^3*c^2 + b^2*c^3 + b^2*c^2) := by
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
  have hn : 0 ≤ (a^3*b^3 + a^3*b^2 + a^3*c^3 + a^3*c^2 + a^2*b^3 - 3*a^2*b^2*c^2 - 2*a^2*b^2*c + a^2*b^2 - 2*a^2*b*c^2 - a^2*b*c + a^2*c^3 + a^2*c^2 - 2*a*b^2*c^2 - a*b^2*c - a*b*c^2 + b^3*c^3 + b^3*c^2 + b^2*c^3 + b^2*c^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b * c) / (a + a^2) + (b + c * a) / (b + b^2) + (c + a * b) / (c + c^2) ≥ 3) := @solution
#print axioms solution
