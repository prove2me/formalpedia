-- Prove2me | solution 1 for WorkbookSource.base_17694
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:10:10.382313+00:00
-- url     : https://prove2.me/submissions/90a1b97d-5220-4a92-bd3d-d488be746747

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a + b + c) ≥ a^3 / (a^2 + a * b + b^2) + b^3 / (b^2 + b * c + c^2) + c^3 / (c^2 + c * a + a^2) + 8 * (a * b + b * c + c * a) / (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6*b^2 + 2*a^6*b*c + 2*a^6*c^2 - a^5*b^3 - a^5*b^2*c - a^5*b*c^2 - a^5*c^3 + 2*a^4*b^4 - 2*a^4*b^3*c + 2*a^4*b^2*c^2 - 2*a^4*b*c^3 + 2*a^4*c^4 - a^3*b^5 - 2*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 2*a^3*b*c^4 - a^3*c^5 + 2*a^2*b^6 - a^2*b^5*c + 2*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 2*a^2*b^2*c^4 - a^2*b*c^5 + 2*a^2*c^6 + 2*a*b^6*c - a*b^5*c^2 - 2*a*b^4*c^3 - 2*a*b^3*c^4 - a*b^2*c^5 + 2*a*b*c^6 + 2*b^6*c^2 - b^5*c^3 + 2*b^4*c^4 - b^3*c^5 + 2*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^6 * (b - a)^2 + (36 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^6 * (c - b)^2 + (138 : ℝ) * a^5 * (b - a)^3 + (207 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (225 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (78 : ℝ) * a^5 * (c - b)^3 + (222 : ℝ) * a^4 * (b - a)^4 + (444 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (561 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (339 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (72 : ℝ) * a^4 * (c - b)^4 + (196 : ℝ) * a^3 * (b - a)^5 + (490 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (712 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (578 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (224 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (32 : ℝ) * a^3 * (c - b)^5 + (102 : ℝ) * a^2 * (b - a)^6 + (306 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (498 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (486 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (258 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (66 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (6 : ℝ) * a^2 * (c - b)^6 + (30 : ℝ) * a^1 * (b - a)^7 + (105 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (187 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (205 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (131 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (44 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * (b - a)^8 + (16 : ℝ) * (b - a)^7 * (c - b)^1 + (31 : ℝ) * (b - a)^6 * (c - b)^2 + (37 : ℝ) * (b - a)^5 * (c - b)^3 + (27 : ℝ) * (b - a)^4 * (c - b)^4 + (11 : ℝ) * (b - a)^3 * (c - b)^5 + (2 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6*b^2 + 2*a^6*b*c + 2*a^6*c^2 - a^5*b^3 - a^5*b^2*c - a^5*b*c^2 - a^5*c^3 + 2*a^4*b^4 - 2*a^4*b^3*c + 2*a^4*b^2*c^2 - 2*a^4*b*c^3 + 2*a^4*c^4 - a^3*b^5 - 2*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 2*a^3*b*c^4 - a^3*c^5 + 2*a^2*b^6 - a^2*b^5*c + 2*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 2*a^2*b^2*c^4 - a^2*b*c^5 + 2*a^2*c^6 + 2*a*b^6*c - a*b^5*c^2 - 2*a*b^4*c^3 - 2*a*b^3*c^4 - a*b^2*c^5 + 2*a*b*c^6 + 2*b^6*c^2 - b^5*c^3 + 2*b^4*c^4 - b^3*c^5 + 2*b^2*c^6) := by
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
  have hn : 0 ≤ (2*a^6*b^2 + 2*a^6*b*c + 2*a^6*c^2 - a^5*b^3 - a^5*b^2*c - a^5*b*c^2 - a^5*c^3 + 2*a^4*b^4 - 2*a^4*b^3*c + 2*a^4*b^2*c^2 - 2*a^4*b*c^3 + 2*a^4*c^4 - a^3*b^5 - 2*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 2*a^3*b*c^4 - a^3*c^5 + 2*a^2*b^6 - a^2*b^5*c + 2*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 2*a^2*b^2*c^4 - a^2*b*c^5 + 2*a^2*c^6 + 2*a*b^6*c - a*b^5*c^2 - 2*a*b^4*c^3 - 2*a*b^3*c^4 - a*b^2*c^5 + 2*a*b*c^6 + 2*b^6*c^2 - b^5*c^3 + 2*b^4*c^4 - b^3*c^5 + 2*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 3 * (a + b + c) ≥ a^3 / (a^2 + a * b + b^2) + b^3 / (b^2 + b * c + c^2) + c^3 / (c^2 + c * a + a^2) + 8 * (a * b + b * c + c * a) / (a + b + c)) := @solution
#print axioms solution
