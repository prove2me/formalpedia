-- Prove2me | solution 1 for WorkbookSource.base_10174
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:46:44.808775+00:00
-- url     : https://prove2.me/submissions/a0d4a94d-b8f3-4904-9d60-75697b815c15

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a * (a + b)) + 1 / (b * (b + c)) + 1 / (c * (c + a))) ≥ 27 / 2 / (a + b + c) ^ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 8*a^4*b*c + 6*a^4*c^2 + 6*a^3*b^3 - 9*a^3*b^2*c - 7*a^3*b*c^2 + 6*a^3*c^3 + 6*a^2*b^4 - 7*a^2*b^3*c - 24*a^2*b^2*c^2 - 9*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 8*a*b^4*c - 9*a*b^3*c^2 - 7*a*b^2*c^3 + 8*a*b*c^4 + 2*b^4*c^2 + 6*b^3*c^3 + 6*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^4 * (b - a)^2 + (72 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (72 : ℝ) * a^4 * (c - b)^2 + (208 : ℝ) * a^3 * (b - a)^3 + (339 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (291 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (80 : ℝ) * a^3 * (c - b)^3 + (218 : ℝ) * a^2 * (b - a)^4 + (490 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (471 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (199 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (26 : ℝ) * a^2 * (c - b)^4 + (98 : ℝ) * a^1 * (b - a)^5 + (281 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (322 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (175 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (40 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^6 + (56 : ℝ) * (b - a)^5 * (c - b)^1 + (76 : ℝ) * (b - a)^4 * (c - b)^2 + (50 : ℝ) * (b - a)^3 * (c - b)^3 + (16 : ℝ) * (b - a)^2 * (c - b)^4 + (2 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 8*a^4*b*c + 6*a^4*c^2 + 6*a^3*b^3 - 9*a^3*b^2*c - 7*a^3*b*c^2 + 6*a^3*c^3 + 6*a^2*b^4 - 7*a^2*b^3*c - 24*a^2*b^2*c^2 - 9*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 8*a*b^4*c - 9*a*b^3*c^2 - 7*a*b^2*c^3 + 8*a*b*c^4 + 2*b^4*c^2 + 6*b^3*c^3 + 6*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^4 * (c - a)^2 + (72 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (72 : ℝ) * a^4 * (b - c)^2 + (208 : ℝ) * a^3 * (c - a)^3 + (285 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (237 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (80 : ℝ) * a^3 * (b - c)^3 + (218 : ℝ) * a^2 * (c - a)^4 + (382 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (309 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (145 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (26 : ℝ) * a^2 * (b - c)^4 + (98 : ℝ) * a^1 * (c - a)^5 + (209 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (178 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (85 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (22 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^1 * (b - c)^5 + (16 : ℝ) * (c - a)^6 + (40 : ℝ) * (c - a)^5 * (b - c)^1 + (36 : ℝ) * (c - a)^4 * (b - c)^2 + (14 : ℝ) * (c - a)^3 * (b - c)^3 + (2 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 8*a^4*b*c + 6*a^4*c^2 + 6*a^3*b^3 - 9*a^3*b^2*c - 7*a^3*b*c^2 + 6*a^3*c^3 + 6*a^2*b^4 - 7*a^2*b^3*c - 24*a^2*b^2*c^2 - 9*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 8*a*b^4*c - 9*a*b^3*c^2 - 7*a*b^2*c^3 + 8*a*b*c^4 + 2*b^4*c^2 + 6*b^3*c^3 + 6*b^2*c^4 + 2*b*c^5) := by
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
  have hn : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 8*a^4*b*c + 6*a^4*c^2 + 6*a^3*b^3 - 9*a^3*b^2*c - 7*a^3*b*c^2 + 6*a^3*c^3 + 6*a^2*b^4 - 7*a^2*b^3*c - 24*a^2*b^2*c^2 - 9*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 8*a*b^4*c - 9*a*b^3*c^2 - 7*a*b^2*c^3 + 8*a*b*c^4 + 2*b^4*c^2 + 6*b^3*c^3 + 6*b^2*c^4 + 2*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (a * (a + b)) + 1 / (b * (b + c)) + 1 / (c * (c + a))) ≥ 27 / 2 / (a + b + c) ^ 2) := @solution
#print axioms solution
