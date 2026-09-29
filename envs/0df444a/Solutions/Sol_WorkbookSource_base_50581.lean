-- Prove2me | solution 1 for WorkbookSource.base_50581
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:45:01.252671+00:00
-- url     : https://prove2.me/submissions/cbb35d2a-79b5-4d71-acf3-6d97d740c9f1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b)) ≥ (a + b + c) / 2 + (a - b)^2 / (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5 + a^4*b + a^4*c + a^3*b^2 - 3*a^3*c^2 + a^2*b^3 - 2*a^2*b^2*c - 4*a^2*b*c^2 - a^2*c^3 + a*b^4 - 4*a*b^2*c^2 + 3*a*c^4 + 2*b^5 + b^4*c - 3*b^3*c^2 - b^2*c^3 + 3*b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^3 * (b - a)^2 + (36 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^3 * (c - b)^2 + (34 : ℝ) * a^2 * (b - a)^3 + (83 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (117 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (42 : ℝ) * a^2 * (c - b)^3 + (20 : ℝ) * a^1 * (b - a)^4 + (60 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (110 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (74 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (16 : ℝ) * a^1 * (c - b)^4 + (4 : ℝ) * (b - a)^5 + (14 : ℝ) * (b - a)^4 * (c - b)^1 + (32 : ℝ) * (b - a)^3 * (c - b)^2 + (31 : ℝ) * (b - a)^2 * (c - b)^3 + (13 : ℝ) * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5 + a^4*b + a^4*c + a^3*b^2 - 3*a^3*c^2 + a^2*b^3 - 2*a^2*b^2*c - 4*a^2*b*c^2 - a^2*c^3 + a*b^4 - 4*a*b^2*c^2 + 3*a*c^4 + 2*b^5 + b^4*c - 3*b^3*c^2 - b^2*c^3 + 3*b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^3 * (c - a)^2 + (4 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (20 : ℝ) * a^3 * (b - c)^2 + (34 : ℝ) * a^2 * (c - a)^3 + (19 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (53 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (26 : ℝ) * a^2 * (b - c)^3 + (20 : ℝ) * a^1 * (c - a)^4 + (20 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (50 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (46 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (12 : ℝ) * a^1 * (b - c)^4 + (4 : ℝ) * (c - a)^5 + (6 : ℝ) * (c - a)^4 * (b - c)^1 + (16 : ℝ) * (c - a)^3 * (b - c)^2 + (21 : ℝ) * (c - a)^2 * (b - c)^3 + (11 : ℝ) * (c - a)^1 * (b - c)^4 + (2 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ c) (hord1 : c ≤ a) (hord2 : a ≤ b) : 0 ≤ (2*a^5 + a^4*b + a^4*c + a^3*b^2 - 3*a^3*c^2 + a^2*b^3 - 2*a^2*b^2*c - 4*a^2*b*c^2 - a^2*c^3 + a*b^4 - 4*a*b^2*c^2 + 3*a*c^4 + 2*b^5 + b^4*c - 3*b^3*c^2 - b^2*c^3 + 3*b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (a - c) := by linarith
    have hdiff2 : 0 ≤ (b - a) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * c^3 * (a - c)^2 + (36 : ℝ) * c^3 * (a - c)^1 * (b - a)^1 + (20 : ℝ) * c^3 * (b - a)^2 + (66 : ℝ) * c^2 * (a - c)^3 + (99 : ℝ) * c^2 * (a - c)^2 * (b - a)^1 + (85 : ℝ) * c^2 * (a - c)^1 * (b - a)^2 + (26 : ℝ) * c^2 * (b - a)^3 + (40 : ℝ) * c^1 * (a - c)^4 + (80 : ℝ) * c^1 * (a - c)^3 * (b - a)^1 + (94 : ℝ) * c^1 * (a - c)^2 * (b - a)^2 + (54 : ℝ) * c^1 * (a - c)^1 * (b - a)^3 + (12 : ℝ) * c^1 * (b - a)^4 + (8 : ℝ) * (a - c)^5 + (20 : ℝ) * (a - c)^4 * (b - a)^1 + (30 : ℝ) * (a - c)^3 * (b - a)^2 + (25 : ℝ) * (a - c)^2 * (b - a)^3 + (11 : ℝ) * (a - c)^1 * (b - a)^4 + (2 : ℝ) * (b - a)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5 + a^4*b + a^4*c + a^3*b^2 - 3*a^3*c^2 + a^2*b^3 - 2*a^2*b^2*c - 4*a^2*b*c^2 - a^2*c^3 + a*b^4 - 4*a*b^2*c^2 + 3*a*c^4 + 2*b^5 + b^4*c - 3*b^3*c^2 - b^2*c^3 + 3*b*c^4 + 2*c^5) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux1 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (2*a^5 + a^4*b + a^4*c + a^3*b^2 - 3*a^3*c^2 + a^2*b^3 - 2*a^2*b^2*c - 4*a^2*b*c^2 - a^2*c^3 + a*b^4 - 4*a*b^2*c^2 + 3*a*c^4 + 2*b^5 + b^4*c - 3*b^3*c^2 - b^2*c^3 + 3*b*c^4 + 2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b)) ≥ (a + b + c) / 2 + (a - b)^2 / (a + b + c)) := @solution
#print axioms solution
