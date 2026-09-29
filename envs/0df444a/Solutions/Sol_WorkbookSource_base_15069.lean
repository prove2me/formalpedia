-- Prove2me | solution 1 for WorkbookSource.base_15069
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:58:17.39125+00:00
-- url     : https://prove2.me/submissions/c632590c-b9b9-42f1-a44b-cbc95d6b4c56

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4 * a - b - c) ^ 2 / (c ^ 2 + a * b) + (4 * b - c - a) ^ 2 / (a ^ 2 + b * c) + (4 * c - a - b) ^ 2 / (b ^ 2 + c * a) ≥ 6  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b + 16*a^5*c + 18*a^4*b^2 - 21*a^4*b*c - 7*a^4*c^2 - 12*a^3*b^3 - 22*a^3*b^2*c + 38*a^3*b*c^2 - 12*a^3*c^3 - 7*a^2*b^4 + 38*a^2*b^3*c - 33*a^2*b^2*c^2 - 22*a^2*b*c^3 + 18*a^2*c^4 + 16*a*b^5 - 21*a*b^4*c - 22*a*b^3*c^2 + 38*a*b^2*c^3 - 21*a*b*c^4 + a*c^5 + b^5*c + 18*b^4*c^2 - 12*b^3*c^3 - 7*b^2*c^4 + 16*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (80 : ℝ) * a^4 * (b - a)^2 + (80 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (80 : ℝ) * a^4 * (c - b)^2 + (198 : ℝ) * a^3 * (b - a)^3 + (302 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (348 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (122 : ℝ) * a^3 * (c - b)^3 + (189 : ℝ) * a^2 * (b - a)^4 + (388 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (537 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (338 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (75 : ℝ) * a^2 * (c - b)^4 + (87 : ℝ) * a^1 * (b - a)^5 + (235 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (376 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (324 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (130 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (17 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^6 + (53 : ℝ) * (b - a)^5 * (c - b)^1 + (100 : ℝ) * (b - a)^4 * (c - b)^2 + (120 : ℝ) * (b - a)^3 * (c - b)^3 + (73 : ℝ) * (b - a)^2 * (c - b)^4 + (16 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b + 16*a^5*c + 18*a^4*b^2 - 21*a^4*b*c - 7*a^4*c^2 - 12*a^3*b^3 - 22*a^3*b^2*c + 38*a^3*b*c^2 - 12*a^3*c^3 - 7*a^2*b^4 + 38*a^2*b^3*c - 33*a^2*b^2*c^2 - 22*a^2*b*c^3 + 18*a^2*c^4 + 16*a*b^5 - 21*a*b^4*c - 22*a*b^3*c^2 + 38*a*b^2*c^3 - 21*a*b*c^4 + a*c^5 + b^5*c + 18*b^4*c^2 - 12*b^3*c^3 - 7*b^2*c^4 + 16*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (80 : ℝ) * a^4 * (c - a)^2 + (80 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (80 : ℝ) * a^4 * (b - c)^2 + (198 : ℝ) * a^3 * (c - a)^3 + (292 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (338 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (122 : ℝ) * a^3 * (b - c)^3 + (189 : ℝ) * a^2 * (c - a)^4 + (368 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (507 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (328 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (75 : ℝ) * a^2 * (b - c)^4 + (87 : ℝ) * a^1 * (c - a)^5 + (200 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (306 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (264 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (105 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (17 : ℝ) * a^1 * (b - c)^5 + (16 : ℝ) * (c - a)^6 + (43 : ℝ) * (c - a)^5 * (b - c)^1 + (75 : ℝ) * (c - a)^4 * (b - c)^2 + (70 : ℝ) * (c - a)^3 * (b - c)^3 + (23 : ℝ) * (c - a)^2 * (b - c)^4 + (1 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b + 16*a^5*c + 18*a^4*b^2 - 21*a^4*b*c - 7*a^4*c^2 - 12*a^3*b^3 - 22*a^3*b^2*c + 38*a^3*b*c^2 - 12*a^3*c^3 - 7*a^2*b^4 + 38*a^2*b^3*c - 33*a^2*b^2*c^2 - 22*a^2*b*c^3 + 18*a^2*c^4 + 16*a*b^5 - 21*a*b^4*c - 22*a*b^3*c^2 + 38*a*b^2*c^3 - 21*a*b*c^4 + a*c^5 + b^5*c + 18*b^4*c^2 - 12*b^3*c^3 - 7*b^2*c^4 + 16*b*c^5) := by
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
  have hn : 0 ≤ (a^5*b + 16*a^5*c + 18*a^4*b^2 - 21*a^4*b*c - 7*a^4*c^2 - 12*a^3*b^3 - 22*a^3*b^2*c + 38*a^3*b*c^2 - 12*a^3*c^3 - 7*a^2*b^4 + 38*a^2*b^3*c - 33*a^2*b^2*c^2 - 22*a^2*b*c^3 + 18*a^2*c^4 + 16*a*b^5 - 21*a*b^4*c - 22*a*b^3*c^2 + 38*a*b^2*c^3 - 21*a*b*c^4 + a*c^5 + b^5*c + 18*b^4*c^2 - 12*b^3*c^3 - 7*b^2*c^4 + 16*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (4 * a - b - c) ^ 2 / (c ^ 2 + a * b) + (4 * b - c - a) ^ 2 / (a ^ 2 + b * c) + (4 * c - a - b) ^ 2 / (b ^ 2 + c * a) ≥ 6) := @solution
#print axioms solution
