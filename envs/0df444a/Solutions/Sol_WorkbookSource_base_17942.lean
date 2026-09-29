-- Prove2me | solution 1 for WorkbookSource.base_17942
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:13:34.12826+00:00
-- url     : https://prove2.me/submissions/acaf5547-473d-4846-8163-d7d51c09d1c6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^3 + b^3) / (a^2 + a * b + b^2) + (b^3 + c^3) / (b^2 + b * c + c^2) + (c^3 + a^3) / (c^2 + c * a + a^2) ≥ (2 / 3) * (a^2 + b^2 + c^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 + 2*a^5*c^3 - 4*a^4*b^2*c^2 + 2*a^3*b^5 - 4*a^3*b^3*c^2 - 4*a^3*b^2*c^3 + 2*a^3*c^5 + 2*a^2*b^5*c - 4*a^2*b^4*c^2 - 4*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 2*a^2*b*c^5 + 2*a*b^5*c^2 + 2*a*b^2*c^5 + 2*b^5*c^3 + 2*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^6 * (b - a)^2 + (36 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^6 * (c - b)^2 + (156 : ℝ) * a^5 * (b - a)^3 + (234 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (198 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (60 : ℝ) * a^5 * (c - b)^3 + (276 : ℝ) * a^4 * (b - a)^4 + (552 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (498 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (222 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (36 : ℝ) * a^4 * (c - b)^4 + (256 : ℝ) * a^3 * (b - a)^5 + (640 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (664 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (356 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (92 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (8 : ℝ) * a^3 * (c - b)^5 + (132 : ℝ) * a^2 * (b - a)^6 + (396 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (480 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (300 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (96 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (12 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (36 : ℝ) * a^1 * (b - a)^7 + (126 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (178 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (130 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (50 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (8 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (4 : ℝ) * (b - a)^8 + (16 : ℝ) * (b - a)^7 * (c - b)^1 + (26 : ℝ) * (b - a)^6 * (c - b)^2 + (22 : ℝ) * (b - a)^5 * (c - b)^3 + (10 : ℝ) * (b - a)^4 * (c - b)^4 + (2 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 + 2*a^5*c^3 - 4*a^4*b^2*c^2 + 2*a^3*b^5 - 4*a^3*b^3*c^2 - 4*a^3*b^2*c^3 + 2*a^3*c^5 + 2*a^2*b^5*c - 4*a^2*b^4*c^2 - 4*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 2*a^2*b*c^5 + 2*a*b^5*c^2 + 2*a*b^2*c^5 + 2*b^5*c^3 + 2*b^3*c^5) := by
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
  have he : (-2*a^6*b^2 - 2*a^6*b*c - 2*a^6*c^2 - 2*a^5*b^3 - 4*a^5*b^2*c + 6*a^5*b^2 - 4*a^5*b*c^2 + 6*a^5*b*c - 2*a^5*c^3 + 6*a^5*c^2 - 4*a^4*b^4 - 6*a^4*b^3*c + 6*a^4*b^3 - 10*a^4*b^2*c^2 + 6*a^4*b^2*c - 6*a^4*b*c^3 + 6*a^4*b*c^2 - 4*a^4*c^4 + 6*a^4*c^3 - 2*a^3*b^5 - 6*a^3*b^4*c + 6*a^3*b^4 - 10*a^3*b^3*c^2 + 6*a^3*b^3*c - 10*a^3*b^2*c^3 + 6*a^3*b^2*c^2 - 6*a^3*b*c^4 + 6*a^3*b*c^3 - 2*a^3*c^5 + 6*a^3*c^4 - 2*a^2*b^6 - 4*a^2*b^5*c + 6*a^2*b^5 - 10*a^2*b^4*c^2 + 6*a^2*b^4*c - 10*a^2*b^3*c^3 + 6*a^2*b^3*c^2 - 10*a^2*b^2*c^4 + 6*a^2*b^2*c^3 - 4*a^2*b*c^5 + 6*a^2*b*c^4 - 2*a^2*c^6 + 6*a^2*c^5 - 2*a*b^6*c - 4*a*b^5*c^2 + 6*a*b^5*c - 6*a*b^4*c^3 + 6*a*b^4*c^2 - 6*a*b^3*c^4 + 6*a*b^3*c^3 - 4*a*b^2*c^5 + 6*a*b^2*c^4 - 2*a*b*c^6 + 6*a*b*c^5 - 2*b^6*c^2 - 2*b^5*c^3 + 6*b^5*c^2 - 4*b^4*c^4 + 6*b^4*c^3 - 2*b^3*c^5 + 6*b^3*c^4 - 2*b^2*c^6 + 6*b^2*c^5) = (2*a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 + 2*a^5*c^3 - 4*a^4*b^2*c^2 + 2*a^3*b^5 - 4*a^3*b^3*c^2 - 4*a^3*b^2*c^3 + 2*a^3*c^5 + 2*a^2*b^5*c - 4*a^2*b^4*c^2 - 4*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 2*a^2*b*c^5 + 2*a*b^5*c^2 + 2*a*b^2*c^5 + 2*b^5*c^3 + 2*b^3*c^5) := by
    linear_combination (-2*a^5*b^2 - 2*a^5*b*c - 2*a^5*c^2 - 2*a^4*b^3 - 2*a^4*b^2*c - 2*a^4*b*c^2 - 2*a^4*c^3 - 2*a^3*b^4 - 2*a^3*b^3*c - 2*a^3*b^2*c^2 - 2*a^3*b*c^3 - 2*a^3*c^4 - 2*a^2*b^5 - 2*a^2*b^4*c - 2*a^2*b^3*c^2 - 2*a^2*b^2*c^3 - 2*a^2*b*c^4 - 2*a^2*c^5 - 2*a*b^5*c - 2*a*b^4*c^2 - 2*a*b^3*c^3 - 2*a*b^2*c^4 - 2*a*b*c^5 - 2*b^5*c^2 - 2*b^4*c^3 - 2*b^3*c^4 - 2*b^2*c^5) * habc
  have hn : 0 ≤ (-2*a^6*b^2 - 2*a^6*b*c - 2*a^6*c^2 - 2*a^5*b^3 - 4*a^5*b^2*c + 6*a^5*b^2 - 4*a^5*b*c^2 + 6*a^5*b*c - 2*a^5*c^3 + 6*a^5*c^2 - 4*a^4*b^4 - 6*a^4*b^3*c + 6*a^4*b^3 - 10*a^4*b^2*c^2 + 6*a^4*b^2*c - 6*a^4*b*c^3 + 6*a^4*b*c^2 - 4*a^4*c^4 + 6*a^4*c^3 - 2*a^3*b^5 - 6*a^3*b^4*c + 6*a^3*b^4 - 10*a^3*b^3*c^2 + 6*a^3*b^3*c - 10*a^3*b^2*c^3 + 6*a^3*b^2*c^2 - 6*a^3*b*c^4 + 6*a^3*b*c^3 - 2*a^3*c^5 + 6*a^3*c^4 - 2*a^2*b^6 - 4*a^2*b^5*c + 6*a^2*b^5 - 10*a^2*b^4*c^2 + 6*a^2*b^4*c - 10*a^2*b^3*c^3 + 6*a^2*b^3*c^2 - 10*a^2*b^2*c^4 + 6*a^2*b^2*c^3 - 4*a^2*b*c^5 + 6*a^2*b*c^4 - 2*a^2*c^6 + 6*a^2*c^5 - 2*a*b^6*c - 4*a*b^5*c^2 + 6*a*b^5*c - 6*a*b^4*c^3 + 6*a*b^4*c^2 - 6*a*b^3*c^4 + 6*a*b^3*c^3 - 4*a*b^2*c^5 + 6*a*b^2*c^4 - 2*a*b*c^6 + 6*a*b*c^5 - 2*b^6*c^2 - 2*b^5*c^3 + 6*b^5*c^2 - 4*b^4*c^4 + 6*b^4*c^3 - 2*b^3*c^5 + 6*b^3*c^4 - 2*b^2*c^6 + 6*b^2*c^5) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^3 + b^3) / (a^2 + a * b + b^2) + (b^3 + c^3) / (b^2 + b * c + c^2) + (c^3 + a^3) / (c^2 + c * a + a^2) ≥ (2 / 3) * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
