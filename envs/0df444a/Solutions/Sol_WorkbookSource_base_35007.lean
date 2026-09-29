-- Prove2me | solution 1 for WorkbookSource.base_35007
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:21.28049+00:00
-- url     : https://prove2.me/submissions/0c90549d-0b96-43d2-892f-b508850f9e32

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a ^ 2 + 7 * a * b + b ^ 2) + 1 / (b ^ 2 + 7 * b * c + c ^ 2) + 1 / (c ^ 2 + 7 * c * a + a ^ 2) ≥ 1 / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b + a^5*c + 6*a^4*b^2 + 8*a^4*b*c + 6*a^4*c^2 - 4*a^3*b^3 + 17*a^3*b^2*c + 17*a^3*b*c^2 - 4*a^3*c^3 + 6*a^2*b^4 + 17*a^2*b^3*c - 156*a^2*b^2*c^2 + 17*a^2*b*c^3 + 6*a^2*c^4 + a*b^5 + 8*a*b^4*c + 17*a*b^3*c^2 + 17*a*b^2*c^3 + 8*a*b*c^4 + a*c^5 + b^5*c + 6*b^4*c^2 - 4*b^3*c^3 + 6*b^2*c^4 + b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (108 : ℝ) * a^4 * (b - a)^2 + (108 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (108 : ℝ) * a^4 * (c - b)^2 + (306 : ℝ) * a^3 * (b - a)^3 + (459 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (405 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (126 : ℝ) * a^3 * (c - b)^3 + (300 : ℝ) * a^2 * (b - a)^4 + (600 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (549 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (249 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (30 : ℝ) * a^2 * (c - b)^4 + (112 : ℝ) * a^1 * (b - a)^5 + (280 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (286 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (149 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (35 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (10 : ℝ) * (b - a)^6 + (30 : ℝ) * (b - a)^5 * (c - b)^1 + (40 : ℝ) * (b - a)^4 * (c - b)^2 + (30 : ℝ) * (b - a)^3 * (c - b)^3 + (11 : ℝ) * (b - a)^2 * (c - b)^4 + (1 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b + a^5*c + 6*a^4*b^2 + 8*a^4*b*c + 6*a^4*c^2 - 4*a^3*b^3 + 17*a^3*b^2*c + 17*a^3*b*c^2 - 4*a^3*c^3 + 6*a^2*b^4 + 17*a^2*b^3*c - 156*a^2*b^2*c^2 + 17*a^2*b*c^3 + 6*a^2*c^4 + a*b^5 + 8*a*b^4*c + 17*a*b^3*c^2 + 17*a*b^2*c^3 + 8*a*b*c^4 + a*c^5 + b^5*c + 6*b^4*c^2 - 4*b^3*c^3 + 6*b^2*c^4 + b*c^5) := by
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
  have hn : 0 ≤ (a^5*b + a^5*c + 6*a^4*b^2 + 8*a^4*b*c + 6*a^4*c^2 - 4*a^3*b^3 + 17*a^3*b^2*c + 17*a^3*b*c^2 - 4*a^3*c^3 + 6*a^2*b^4 + 17*a^2*b^3*c - 156*a^2*b^2*c^2 + 17*a^2*b*c^3 + 6*a^2*c^4 + a*b^5 + 8*a*b^4*c + 17*a*b^3*c^2 + 17*a*b^2*c^3 + 8*a*b*c^4 + a*c^5 + b^5*c + 6*b^4*c^2 - 4*b^3*c^3 + 6*b^2*c^4 + b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 1 / (a ^ 2 + 7 * a * b + b ^ 2) + 1 / (b ^ 2 + 7 * b * c + c ^ 2) + 1 / (c ^ 2 + 7 * c * a + a ^ 2) ≥ 1 / (a * b + b * c + c * a)) := @solution
#print axioms solution
