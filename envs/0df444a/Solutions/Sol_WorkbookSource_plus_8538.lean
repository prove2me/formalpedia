-- Prove2me | solution 1 for WorkbookSource.plus_8538
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:18.737818+00:00
-- url     : https://prove2.me/submissions/4bf64a84-a90c-4bd0-80a2-e6729fb68aea

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ^ 2 ≥ (a + b + c) * (1 / a + 1 / b + 1 / c) + 2 * ((b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) / (b * c + c * a + a * b)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b*c^2 + a^5*c^3 + a^4*b^3*c - 4*a^4*b^2*c^2 + a^3*b^5 + a^3*b^3*c^2 + a^3*b^2*c^3 + a^3*b*c^4 + a^2*b^5*c - 4*a^2*b^4*c^2 + a^2*b^3*c^3 - 4*a^2*b^2*c^4 + a*b^4*c^3 + a*b^2*c^5 + b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^6 * (b - a)^2 + (8 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^6 * (c - b)^2 + (36 : ℝ) * a^5 * (b - a)^3 + (63 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (51 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^5 * (c - b)^3 + (67 : ℝ) * a^4 * (b - a)^4 + (164 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (156 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (59 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (7 : ℝ) * a^4 * (c - b)^4 + (66 : ℝ) * a^3 * (b - a)^5 + (204 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (240 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (126 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (28 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^3 * (c - b)^5 + (36 : ℝ) * a^2 * (b - a)^6 + (133 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (190 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (129 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (41 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (5 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (10 : ℝ) * a^1 * (b - a)^7 + (43 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (73 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (61 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (25 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (4 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^8 + (5 : ℝ) * (b - a)^7 * (c - b)^1 + (10 : ℝ) * (b - a)^6 * (c - b)^2 + (10 : ℝ) * (b - a)^5 * (c - b)^3 + (5 : ℝ) * (b - a)^4 * (c - b)^4 + (1 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b*c^2 + a^5*c^3 + a^4*b^3*c - 4*a^4*b^2*c^2 + a^3*b^5 + a^3*b^3*c^2 + a^3*b^2*c^3 + a^3*b*c^4 + a^2*b^5*c - 4*a^2*b^4*c^2 + a^2*b^3*c^3 - 4*a^2*b^2*c^4 + a*b^4*c^3 + a*b^2*c^5 + b^3*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^6 * (c - a)^2 + (8 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (8 : ℝ) * a^6 * (b - c)^2 + (36 : ℝ) * a^5 * (c - a)^3 + (45 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (33 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (12 : ℝ) * a^5 * (b - c)^3 + (67 : ℝ) * a^4 * (c - a)^4 + (104 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (66 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (29 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (7 : ℝ) * a^4 * (b - c)^4 + (66 : ℝ) * a^3 * (c - a)^5 + (126 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (84 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (30 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (10 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^3 * (b - c)^5 + (36 : ℝ) * a^2 * (c - a)^6 + (83 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (65 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (21 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (4 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (1 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (10 : ℝ) * a^1 * (c - a)^7 + (27 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (25 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (9 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (1 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (1 : ℝ) * (c - a)^8 + (3 : ℝ) * (c - a)^7 * (b - c)^1 + (3 : ℝ) * (c - a)^6 * (b - c)^2 + (1 : ℝ) * (c - a)^5 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b*c^2 + a^5*c^3 + a^4*b^3*c - 4*a^4*b^2*c^2 + a^3*b^5 + a^3*b^3*c^2 + a^3*b^2*c^3 + a^3*b*c^4 + a^2*b^5*c - 4*a^2*b^4*c^2 + a^2*b^3*c^3 - 4*a^2*b^2*c^4 + a*b^4*c^3 + a*b^2*c^5 + b^3*c^5) := by
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
  have hn : 0 ≤ (a^5*b*c^2 + a^5*c^3 + a^4*b^3*c - 4*a^4*b^2*c^2 + a^3*b^5 + a^3*b^3*c^2 + a^3*b^2*c^3 + a^3*b*c^4 + a^2*b^5*c - 4*a^2*b^4*c^2 + a^2*b^3*c^3 - 4*a^2*b^2*c^4 + a*b^4*c^3 + a*b^2*c^5 + b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / b + b / c + c / a) ^ 2 ≥ (a + b + c) * (1 / a + 1 / b + 1 / c) + 2 * ((b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) / (b * c + c * a + a * b)) := @solution
#print axioms solution
