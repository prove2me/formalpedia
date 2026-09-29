-- Prove2me | solution 1 for WorkbookSource.base_19167
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:39:40.717423+00:00
-- url     : https://prove2.me/submissions/2b40bf3a-50fd-4075-aa0e-af4e5f3673c3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (a^2 + a * b + b^2) + b^2 / (b^2 + b * c + c^2) + c^2 / (c^2 + c * a + a^2)) ≤ (a^2 + b^2 + c^2) / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b^2 + a^6*b*c + a^6*c^2 - a^5*b^3 - a^5*b^2*c + a^4*b^4 - 2*a^4*b^3*c + a^4*b^2*c^2 + a^4*c^4 - a^3*b^3*c^2 - a^3*b^2*c^3 - 2*a^3*b*c^4 - a^3*c^5 + a^2*b^6 + a^2*b^4*c^2 - a^2*b^3*c^3 + a^2*b^2*c^4 - a^2*b*c^5 + a^2*c^6 + a*b^6*c - a*b^5*c^2 - 2*a*b^4*c^3 + a*b*c^6 + b^6*c^2 - b^5*c^3 + b^4*c^4 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (18 : ℝ) * a^6 * (b - a)^2 + (18 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (18 : ℝ) * a^6 * (c - b)^2 + (69 : ℝ) * a^5 * (b - a)^3 + (117 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (126 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (39 : ℝ) * a^5 * (c - b)^3 + (111 : ℝ) * a^4 * (b - a)^4 + (267 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (348 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (192 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (36 : ℝ) * a^4 * (c - b)^4 + (98 : ℝ) * a^3 * (b - a)^5 + (302 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (470 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (358 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (124 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (16 : ℝ) * a^3 * (c - b)^5 + (51 : ℝ) * a^2 * (b - a)^6 + (187 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (334 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (315 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (152 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (35 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (3 : ℝ) * a^2 * (c - b)^6 + (15 : ℝ) * a^1 * (b - a)^7 + (62 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (122 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (133 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (79 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (24 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2 : ℝ) * (b - a)^8 + (9 : ℝ) * (b - a)^7 * (c - b)^1 + (19 : ℝ) * (b - a)^6 * (c - b)^2 + (23 : ℝ) * (b - a)^5 * (c - b)^3 + (16 : ℝ) * (b - a)^4 * (c - b)^4 + (6 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6*b^2 + a^6*b*c + a^6*c^2 - a^5*b^3 - a^5*b^2*c + a^4*b^4 - 2*a^4*b^3*c + a^4*b^2*c^2 + a^4*c^4 - a^3*b^3*c^2 - a^3*b^2*c^3 - 2*a^3*b*c^4 - a^3*c^5 + a^2*b^6 + a^2*b^4*c^2 - a^2*b^3*c^3 + a^2*b^2*c^4 - a^2*b*c^5 + a^2*c^6 + a*b^6*c - a*b^5*c^2 - 2*a*b^4*c^3 + a*b*c^6 + b^6*c^2 - b^5*c^3 + b^4*c^4 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (18 : ℝ) * a^6 * (c - a)^2 + (18 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (18 : ℝ) * a^6 * (b - c)^2 + (69 : ℝ) * a^5 * (c - a)^3 + (90 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (99 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (39 : ℝ) * a^5 * (b - c)^3 + (111 : ℝ) * a^4 * (c - a)^4 + (177 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (213 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (147 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (36 : ℝ) * a^4 * (b - c)^4 + (98 : ℝ) * a^3 * (c - a)^5 + (188 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (242 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (220 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (100 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (16 : ℝ) * a^3 * (b - c)^5 + (51 : ℝ) * a^2 * (c - a)^6 + (119 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (164 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (171 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (106 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (31 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (3 : ℝ) * a^2 * (b - c)^6 + (15 : ℝ) * a^1 * (c - a)^7 + (43 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (65 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (72 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (52 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (20 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (3 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (2 : ℝ) * (c - a)^8 + (7 : ℝ) * (c - a)^7 * (b - c)^1 + (12 : ℝ) * (c - a)^6 * (b - c)^2 + (14 : ℝ) * (c - a)^5 * (b - c)^3 + (11 : ℝ) * (c - a)^4 * (b - c)^4 + (5 : ℝ) * (c - a)^3 * (b - c)^5 + (1 : ℝ) * (c - a)^2 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b^2 + a^6*b*c + a^6*c^2 - a^5*b^3 - a^5*b^2*c + a^4*b^4 - 2*a^4*b^3*c + a^4*b^2*c^2 + a^4*c^4 - a^3*b^3*c^2 - a^3*b^2*c^3 - 2*a^3*b*c^4 - a^3*c^5 + a^2*b^6 + a^2*b^4*c^2 - a^2*b^3*c^3 + a^2*b^2*c^4 - a^2*b*c^5 + a^2*c^6 + a*b^6*c - a*b^5*c^2 - 2*a*b^4*c^3 + a*b*c^6 + b^6*c^2 - b^5*c^3 + b^4*c^4 + b^2*c^6) := by
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
  have hn : 0 ≤ (a^6*b^2 + a^6*b*c + a^6*c^2 - a^5*b^3 - a^5*b^2*c + a^4*b^4 - 2*a^4*b^3*c + a^4*b^2*c^2 + a^4*c^4 - a^3*b^3*c^2 - a^3*b^2*c^3 - 2*a^3*b*c^4 - a^3*c^5 + a^2*b^6 + a^2*b^4*c^2 - a^2*b^3*c^3 + a^2*b^2*c^4 - a^2*b*c^5 + a^2*c^6 + a*b^6*c - a*b^5*c^2 - 2*a*b^4*c^3 + a*b*c^6 + b^6*c^2 - b^5*c^3 + b^4*c^4 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (a^2 + a * b + b^2) + b^2 / (b^2 + b * c + c^2) + c^2 / (c^2 + c * a + a^2)) ≤ (a^2 + b^2 + c^2) / (a * b + b * c + c * a)) := @solution
#print axioms solution
