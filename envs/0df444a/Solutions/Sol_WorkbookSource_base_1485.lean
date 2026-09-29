-- Prove2me | solution 1 for WorkbookSource.base_1485
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:40.8124+00:00
-- url     : https://prove2.me/submissions/9a674f5f-3ba6-4dfd-9632-114397663110

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^3 / (a^2 + a * b + b^2) + b^3 / (b^2 + b * c + c^2) + c^3 / (c^2 + c * a + a^2)) ≥ (a + b + c) / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b^2 + 2*a^5*b*c + 2*a^5*c^2 + a^4*b^3 - a^4*b^2*c - a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 2*a^3*b^3*c - 4*a^3*b^2*c^2 - 2*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^5 - a^2*b^4*c - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 - a^2*b*c^4 + 2*a^2*c^5 + 2*a*b^5*c - a*b^4*c^2 - 2*a*b^3*c^3 - a*b^2*c^4 + 2*a*b*c^5 + 2*b^5*c^2 + b^4*c^3 + b^3*c^4 + 2*b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^5 * (b - a)^2 + (36 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^5 * (c - b)^2 + (126 : ℝ) * a^4 * (b - a)^3 + (189 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (171 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (54 : ℝ) * a^4 * (c - b)^3 + (174 : ℝ) * a^3 * (b - a)^4 + (348 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (342 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (168 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (30 : ℝ) * a^3 * (c - b)^4 + (120 : ℝ) * a^2 * (b - a)^5 + (300 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (336 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (204 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (60 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^2 * (c - b)^5 + (42 : ℝ) * a^1 * (b - a)^6 + (126 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (162 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (114 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (42 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (6 : ℝ) * (b - a)^7 + (21 : ℝ) * (b - a)^6 * (c - b)^1 + (31 : ℝ) * (b - a)^5 * (c - b)^2 + (25 : ℝ) * (b - a)^4 * (c - b)^3 + (11 : ℝ) * (b - a)^3 * (c - b)^4 + (2 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b^2 + 2*a^5*b*c + 2*a^5*c^2 + a^4*b^3 - a^4*b^2*c - a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 2*a^3*b^3*c - 4*a^3*b^2*c^2 - 2*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^5 - a^2*b^4*c - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 - a^2*b*c^4 + 2*a^2*c^5 + 2*a*b^5*c - a*b^4*c^2 - 2*a*b^3*c^3 - a*b^2*c^4 + 2*a*b*c^5 + 2*b^5*c^2 + b^4*c^3 + b^3*c^4 + 2*b^2*c^5) := by
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
  have hn : 0 ≤ (2*a^5*b^2 + 2*a^5*b*c + 2*a^5*c^2 + a^4*b^3 - a^4*b^2*c - a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 2*a^3*b^3*c - 4*a^3*b^2*c^2 - 2*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^5 - a^2*b^4*c - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 - a^2*b*c^4 + 2*a^2*c^5 + 2*a*b^5*c - a*b^4*c^2 - 2*a*b^3*c^3 - a*b^2*c^4 + 2*a*b*c^5 + 2*b^5*c^2 + b^4*c^3 + b^3*c^4 + 2*b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a^3 / (a^2 + a * b + b^2) + b^3 / (b^2 + b * c + c^2) + c^3 / (c^2 + c * a + a^2)) ≥ (a + b + c) / 3) := @solution
#print axioms solution
