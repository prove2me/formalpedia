-- Prove2me | solution 1 for WorkbookSource.base_47159
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:32.659673+00:00
-- url     : https://prove2.me/submissions/46b047cb-9990-4115-807f-deb770bdb909

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 2 * b^2) * (b^2 + 2 * c^2) * (c^2 + 2 * a^2) ≥ 1/3 * (a * b + b * c + c * a)^2 * (a + b + c)^2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^4*b^2 - 2*a^4*b*c + 11*a^4*c^2 - 2*a^3*b^3 - 8*a^3*b^2*c - 8*a^3*b*c^2 - 2*a^3*c^3 + 11*a^2*b^4 - 8*a^2*b^3*c + 12*a^2*b^2*c^2 - 8*a^2*b*c^3 + 5*a^2*c^4 - 2*a*b^4*c - 8*a*b^3*c^2 - 8*a*b^2*c^3 - 2*a*b*c^4 + 5*b^4*c^2 - 2*b^3*c^3 + 11*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^4 * (b - a)^2 + (36 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^4 * (c - b)^2 + (108 : ℝ) * a^3 * (b - a)^3 + (186 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (150 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (36 : ℝ) * a^3 * (c - b)^3 + (122 : ℝ) * a^2 * (b - a)^4 + (292 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (276 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (106 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (14 : ℝ) * a^2 * (c - b)^4 + (64 : ℝ) * a^1 * (b - a)^5 + (190 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (216 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (110 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (20 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (14 : ℝ) * (b - a)^6 + (48 : ℝ) * (b - a)^5 * (c - b)^1 + (65 : ℝ) * (b - a)^4 * (c - b)^2 + (42 : ℝ) * (b - a)^3 * (c - b)^3 + (11 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (5*a^4*b^2 - 2*a^4*b*c + 11*a^4*c^2 - 2*a^3*b^3 - 8*a^3*b^2*c - 8*a^3*b*c^2 - 2*a^3*c^3 + 11*a^2*b^4 - 8*a^2*b^3*c + 12*a^2*b^2*c^2 - 8*a^2*b*c^3 + 5*a^2*c^4 - 2*a*b^4*c - 8*a*b^3*c^2 - 8*a*b^2*c^3 - 2*a*b*c^4 + 5*b^4*c^2 - 2*b^3*c^3 + 11*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^4 * (c - a)^2 + (36 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (36 : ℝ) * a^4 * (b - c)^2 + (108 : ℝ) * a^3 * (c - a)^3 + (138 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (102 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (36 : ℝ) * a^3 * (b - c)^3 + (122 : ℝ) * a^2 * (c - a)^4 + (196 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (132 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (58 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (14 : ℝ) * a^2 * (b - c)^4 + (64 : ℝ) * a^1 * (c - a)^5 + (130 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (96 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (38 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (8 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (14 : ℝ) * (c - a)^6 + (36 : ℝ) * (c - a)^5 * (b - c)^1 + (35 : ℝ) * (c - a)^4 * (b - c)^2 + (18 : ℝ) * (c - a)^3 * (b - c)^3 + (5 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^4*b^2 - 2*a^4*b*c + 11*a^4*c^2 - 2*a^3*b^3 - 8*a^3*b^2*c - 8*a^3*b*c^2 - 2*a^3*c^3 + 11*a^2*b^4 - 8*a^2*b^3*c + 12*a^2*b^2*c^2 - 8*a^2*b*c^3 + 5*a^2*c^4 - 2*a*b^4*c - 8*a*b^3*c^2 - 8*a*b^2*c^3 - 2*a*b*c^4 + 5*b^4*c^2 - 2*b^3*c^3 + 11*b^2*c^4) := by
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
  have hn : 0 ≤ (5*a^4*b^2 - 2*a^4*b*c + 11*a^4*c^2 - 2*a^3*b^3 - 8*a^3*b^2*c - 8*a^3*b*c^2 - 2*a^3*c^3 + 11*a^2*b^4 - 8*a^2*b^3*c + 12*a^2*b^2*c^2 - 8*a^2*b*c^3 + 5*a^2*c^4 - 2*a*b^4*c - 8*a*b^3*c^2 - 8*a*b^2*c^3 - 2*a*b*c^4 + 5*b^4*c^2 - 2*b^3*c^3 + 11*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + 2 * b^2) * (b^2 + 2 * c^2) * (c^2 + 2 * a^2) ≥ 1/3 * (a * b + b * c + c * a)^2 * (a + b + c)^2) := @solution
#print axioms solution
