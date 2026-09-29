-- Prove2me | solution 1 for WorkbookSource.plus_28468
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:43.810035+00:00
-- url     : https://prove2.me/submissions/6b4f5b93-e4eb-4850-a988-3595c4c955c5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / b + b^3 / c + c^3 / a + (a * b + b * c + c * a)^2 / (a^2 + b^2 + c^2)) ≥ (2 * (a + b + c)^2) / 3   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6*c - 2*a^5*b*c - a^4*b^2*c - 4*a^4*b*c^2 + 3*a^4*c^3 + 3*a^3*b^4 - a^3*b^3*c + 2*a^3*b^2*c^2 - a^3*b*c^3 - 4*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 + 3*a*b^6 - 2*a*b^5*c - a*b^4*c^2 - a*b^3*c^3 - 4*a*b^2*c^4 - 2*a*b*c^5 + 3*b^3*c^4 + 3*b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * a^5 * (b - a)^2 + (21 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (21 : ℝ) * a^5 * (c - b)^2 + (70 : ℝ) * a^4 * (b - a)^3 + (132 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (132 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (35 : ℝ) * a^4 * (c - b)^3 + (103 : ℝ) * a^3 * (b - a)^4 + (278 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (347 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (172 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (33 : ℝ) * a^3 * (c - b)^4 + (83 : ℝ) * a^2 * (b - a)^5 + (287 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (440 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (319 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (115 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (16 : ℝ) * a^2 * (c - b)^5 + (35 : ℝ) * a^1 * (b - a)^6 + (147 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (267 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (251 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (130 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (34 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (3 : ℝ) * a^1 * (c - b)^6 + (6 : ℝ) * (b - a)^7 + (30 : ℝ) * (b - a)^6 * (c - b)^1 + (63 : ℝ) * (b - a)^5 * (c - b)^2 + (72 : ℝ) * (b - a)^4 * (c - b)^3 + (48 : ℝ) * (b - a)^3 * (c - b)^4 + (18 : ℝ) * (b - a)^2 * (c - b)^5 + (3 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^6*c - 2*a^5*b*c - a^4*b^2*c - 4*a^4*b*c^2 + 3*a^4*c^3 + 3*a^3*b^4 - a^3*b^3*c + 2*a^3*b^2*c^2 - a^3*b*c^3 - 4*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 + 3*a*b^6 - 2*a*b^5*c - a*b^4*c^2 - a*b^3*c^3 - 4*a*b^2*c^4 - 2*a*b*c^5 + 3*b^3*c^4 + 3*b*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * a^5 * (c - a)^2 + (21 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (21 : ℝ) * a^5 * (b - c)^2 + (70 : ℝ) * a^4 * (c - a)^3 + (78 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (78 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (35 : ℝ) * a^4 * (b - c)^3 + (103 : ℝ) * a^3 * (c - a)^4 + (134 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (131 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (100 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (33 : ℝ) * a^3 * (b - c)^4 + (83 : ℝ) * a^2 * (c - a)^5 + (128 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (122 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (109 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (64 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (16 : ℝ) * a^2 * (b - c)^5 + (35 : ℝ) * a^1 * (c - a)^6 + (63 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (57 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (47 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (34 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (16 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (3 : ℝ) * a^1 * (b - c)^6 + (6 : ℝ) * (c - a)^7 + (12 : ℝ) * (c - a)^6 * (b - c)^1 + (9 : ℝ) * (c - a)^5 * (b - c)^2 + (3 : ℝ) * (c - a)^4 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6*c - 2*a^5*b*c - a^4*b^2*c - 4*a^4*b*c^2 + 3*a^4*c^3 + 3*a^3*b^4 - a^3*b^3*c + 2*a^3*b^2*c^2 - a^3*b*c^3 - 4*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 + 3*a*b^6 - 2*a*b^5*c - a*b^4*c^2 - a*b^3*c^3 - 4*a*b^2*c^4 - 2*a*b*c^5 + 3*b^3*c^4 + 3*b*c^6) := by
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
  have hn : 0 ≤ (3*a^6*c - 2*a^5*b*c - a^4*b^2*c - 4*a^4*b*c^2 + 3*a^4*c^3 + 3*a^3*b^4 - a^3*b^3*c + 2*a^3*b^2*c^2 - a^3*b*c^3 - 4*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 + 3*a*b^6 - 2*a*b^5*c - a*b^4*c^2 - a*b^3*c^3 - 4*a*b^2*c^4 - 2*a*b*c^5 + 3*b^3*c^4 + 3*b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 / b + b^3 / c + c^3 / a + (a * b + b * c + c * a)^2 / (a^2 + b^2 + c^2)) ≥ (2 * (a + b + c)^2) / 3) := @solution
#print axioms solution
