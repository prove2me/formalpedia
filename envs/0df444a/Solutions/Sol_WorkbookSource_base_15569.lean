-- Prove2me | solution 1 for WorkbookSource.base_15569
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:03.379107+00:00
-- url     : https://prove2.me/submissions/c77127b8-9ff3-4ff6-a6e0-775eeee3fe3b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 3 * b^2) / (b + c)^2 + (b^2 + 3 * c^2) / (c + a)^2 + (c^2 + 3 * a^2) / (a + b)^2 ≤ 4 * (a^2 / (b + c)^2 + b^2 / (c + a)^2 + c^2 / (a + b)^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6 + 6*a^5*b + 6*a^5*c - 3*a^4*b^2 + 6*a^4*b*c - 6*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 - 6*a^3*c^3 - 6*a^2*b^3*c - 6*a^2*b*c^3 - 3*a^2*c^4 + 6*a*b^5 + 6*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 + 6*a*b*c^4 + 6*a*c^5 + 3*b^6 + 6*b^5*c - 3*b^4*c^2 - 6*b^3*c^3 + 6*b*c^5 + 3*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^4 * (b - a)^2 + (96 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^4 * (c - b)^2 + (216 : ℝ) * a^3 * (b - a)^3 + (336 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (456 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (168 : ℝ) * a^3 * (c - b)^3 + (180 : ℝ) * a^2 * (b - a)^4 + (384 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (684 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (480 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (108 : ℝ) * a^2 * (c - b)^4 + (66 : ℝ) * a^1 * (b - a)^5 + (180 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (408 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (420 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (186 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (30 : ℝ) * a^1 * (c - b)^5 + (9 : ℝ) * (b - a)^6 + (30 : ℝ) * (b - a)^5 * (c - b)^1 + (84 : ℝ) * (b - a)^4 * (c - b)^2 + (114 : ℝ) * (b - a)^3 * (c - b)^3 + (75 : ℝ) * (b - a)^2 * (c - b)^4 + (24 : ℝ) * (b - a)^1 * (c - b)^5 + (3 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^6 + 6*a^5*b + 6*a^5*c - 3*a^4*b^2 + 6*a^4*b*c - 6*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 - 6*a^3*c^3 - 6*a^2*b^3*c - 6*a^2*b*c^3 - 3*a^2*c^4 + 6*a*b^5 + 6*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 + 6*a*b*c^4 + 6*a*c^5 + 3*b^6 + 6*b^5*c - 3*b^4*c^2 - 6*b^3*c^3 + 6*b*c^5 + 3*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^4 * (c - a)^2 + (96 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (96 : ℝ) * a^4 * (b - c)^2 + (216 : ℝ) * a^3 * (c - a)^3 + (312 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (432 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (168 : ℝ) * a^3 * (b - c)^3 + (180 : ℝ) * a^2 * (c - a)^4 + (336 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (612 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (456 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (108 : ℝ) * a^2 * (b - c)^4 + (66 : ℝ) * a^1 * (c - a)^5 + (150 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (348 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (384 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (180 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (30 : ℝ) * a^1 * (b - c)^5 + (9 : ℝ) * (c - a)^6 + (24 : ℝ) * (c - a)^5 * (b - c)^1 + (69 : ℝ) * (c - a)^4 * (b - c)^2 + (102 : ℝ) * (c - a)^3 * (b - c)^3 + (72 : ℝ) * (c - a)^2 * (b - c)^4 + (24 : ℝ) * (c - a)^1 * (b - c)^5 + (3 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6 + 6*a^5*b + 6*a^5*c - 3*a^4*b^2 + 6*a^4*b*c - 6*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 - 6*a^3*c^3 - 6*a^2*b^3*c - 6*a^2*b*c^3 - 3*a^2*c^4 + 6*a*b^5 + 6*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 + 6*a*b*c^4 + 6*a*c^5 + 3*b^6 + 6*b^5*c - 3*b^4*c^2 - 6*b^3*c^3 + 6*b*c^5 + 3*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (3*a^6 + 6*a^5*b + 6*a^5*c - 3*a^4*b^2 + 6*a^4*b*c - 6*a^3*b^3 - 6*a^3*b^2*c - 6*a^3*b*c^2 - 6*a^3*c^3 - 6*a^2*b^3*c - 6*a^2*b*c^3 - 3*a^2*c^4 + 6*a*b^5 + 6*a*b^4*c - 6*a*b^3*c^2 - 6*a*b^2*c^3 + 6*a*b*c^4 + 6*a*c^5 + 3*b^6 + 6*b^5*c - 3*b^4*c^2 - 6*b^3*c^3 + 6*b*c^5 + 3*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + 3 * b^2) / (b + c)^2 + (b^2 + 3 * c^2) / (c + a)^2 + (c^2 + 3 * a^2) / (a + b)^2 ≤ 4 * (a^2 / (b + c)^2 + b^2 / (c + a)^2 + c^2 / (a + b)^2)) := @solution
#print axioms solution
