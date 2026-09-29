-- Prove2me | solution 1 for WorkbookSource.base_20200
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:44:28.822587+00:00
-- url     : https://prove2.me/submissions/77396d47-004e-48d1-8905-a614e0146a28

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) * (c / (a + b) + 1 / 2) ≤ 7 / 8 + (a^3 + b^3 + c^3) / (24 * a * b * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b + a^5*c + a^4*b^2 - 4*a^4*b*c + a^4*c^2 + a^3*b^2*c + a^3*b*c^2 + a^2*b^4 + a^2*b^3*c - 6*a^2*b^2*c^2 + a^2*b*c^3 + a^2*c^4 + a*b^5 - 4*a*b^4*c + a*b^3*c^2 + a*b^2*c^3 - 4*a*b*c^4 + a*c^5 + b^5*c + b^4*c^2 + b^2*c^4 + b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^4 * (c - b)^2 + (34 : ℝ) * a^3 * (b - a)^3 + (51 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (45 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (14 : ℝ) * a^3 * (c - b)^3 + (38 : ℝ) * a^2 * (b - a)^4 + (76 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (75 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (37 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^2 * (c - b)^4 + (20 : ℝ) * a^1 * (b - a)^5 + (50 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (58 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (37 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (13 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (17 : ℝ) * (b - a)^4 * (c - b)^2 + (14 : ℝ) * (b - a)^3 * (c - b)^3 + (6 : ℝ) * (b - a)^2 * (c - b)^4 + (1 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b + a^5*c + a^4*b^2 - 4*a^4*b*c + a^4*c^2 + a^3*b^2*c + a^3*b*c^2 + a^2*b^4 + a^2*b^3*c - 6*a^2*b^2*c^2 + a^2*b*c^3 + a^2*c^4 + a*b^5 - 4*a*b^4*c + a*b^3*c^2 + a*b^2*c^3 - 4*a*b*c^4 + a*c^5 + b^5*c + b^4*c^2 + b^2*c^4 + b*c^5) := by
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
  have hn : 0 ≤ (a^5*b + a^5*c + a^4*b^2 - 4*a^4*b*c + a^4*c^2 + a^3*b^2*c + a^3*b*c^2 + a^2*b^4 + a^2*b^3*c - 6*a^2*b^2*c^2 + a^2*b*c^3 + a^2*c^4 + a*b^5 - 4*a*b^4*c + a*b^3*c^2 + a*b^2*c^3 - 4*a*b*c^4 + a*c^5 + b^5*c + b^4*c^2 + b^2*c^4 + b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) * (c / (a + b) + 1 / 2) ≤ 7 / 8 + (a^3 + b^3 + c^3) / (24 * a * b * c)) := @solution
#print axioms solution
