-- Prove2me | solution 1 for WorkbookSource.base_9688
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:45:29.770561+00:00
-- url     : https://prove2.me/submissions/968cb0f4-c70f-433c-b098-5028df1aac3d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b + c) / (a * b + b * c + a * c) ≥ a / (a ^ 2 + b * c + b ^ 2) + b / (b ^ 2 + c * a + c ^ 2) + c / (c ^ 2 + a * b + a ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*c + a^5*c^2 - a^4*b^2*c - 2*a^3*b^3*c + a^3*b^2*c^2 - 2*a^3*b*c^3 + a^2*b^5 + a^2*b^3*c^2 + a^2*b^2*c^3 - a^2*b*c^4 + a*b^6 - a*b^4*c^2 - 2*a*b^3*c^3 + b^2*c^5 + b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^5 * (b - a)^2 + (12 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^5 * (c - b)^2 + (37 : ℝ) * a^4 * (b - a)^3 + (72 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (81 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (23 : ℝ) * a^4 * (c - b)^3 + (47 : ℝ) * a^3 * (b - a)^4 + (138 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (197 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (106 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (19 : ℝ) * a^3 * (c - b)^4 + (32 : ℝ) * a^2 * (b - a)^5 + (126 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (220 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (171 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (59 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (7 : ℝ) * a^2 * (c - b)^5 + (12 : ℝ) * a^1 * (b - a)^6 + (58 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (118 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (118 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (60 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (14 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^1 * (c - b)^6 + (2 : ℝ) * (b - a)^7 + (11 : ℝ) * (b - a)^6 * (c - b)^1 + (25 : ℝ) * (b - a)^5 * (c - b)^2 + (30 : ℝ) * (b - a)^4 * (c - b)^3 + (20 : ℝ) * (b - a)^3 * (c - b)^4 + (7 : ℝ) * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6*c + a^5*c^2 - a^4*b^2*c - 2*a^3*b^3*c + a^3*b^2*c^2 - 2*a^3*b*c^3 + a^2*b^5 + a^2*b^3*c^2 + a^2*b^2*c^3 - a^2*b*c^4 + a*b^6 - a*b^4*c^2 - 2*a*b^3*c^3 + b^2*c^5 + b*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^5 * (c - a)^2 + (12 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (12 : ℝ) * a^5 * (b - c)^2 + (37 : ℝ) * a^4 * (c - a)^3 + (39 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (48 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (23 : ℝ) * a^4 * (b - c)^3 + (47 : ℝ) * a^3 * (c - a)^4 + (50 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (65 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (62 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (19 : ℝ) * a^3 * (b - c)^4 + (32 : ℝ) * a^2 * (c - a)^5 + (34 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (36 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (53 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (33 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (7 : ℝ) * a^2 * (b - c)^5 + (12 : ℝ) * a^1 * (c - a)^6 + (14 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (8 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (14 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (14 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (6 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (1 : ℝ) * a^1 * (b - c)^6 + (2 : ℝ) * (c - a)^7 + (3 : ℝ) * (c - a)^6 * (b - c)^1 + (1 : ℝ) * (c - a)^5 * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*c + a^5*c^2 - a^4*b^2*c - 2*a^3*b^3*c + a^3*b^2*c^2 - 2*a^3*b*c^3 + a^2*b^5 + a^2*b^3*c^2 + a^2*b^2*c^3 - a^2*b*c^4 + a*b^6 - a*b^4*c^2 - 2*a*b^3*c^3 + b^2*c^5 + b*c^6) := by
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
  have hn : 0 ≤ (a^6*c + a^5*c^2 - a^4*b^2*c - 2*a^3*b^3*c + a^3*b^2*c^2 - 2*a^3*b*c^3 + a^2*b^5 + a^2*b^3*c^2 + a^2*b^2*c^3 - a^2*b*c^4 + a*b^6 - a*b^4*c^2 - 2*a*b^3*c^3 + b^2*c^5 + b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a + b + c) / (a * b + b * c + a * c) ≥ a / (a ^ 2 + b * c + b ^ 2) + b / (b ^ 2 + c * a + c ^ 2) + c / (c ^ 2 + a * b + a ^ 2)) := @solution
#print axioms solution
