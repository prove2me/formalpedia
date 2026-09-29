-- Prove2me | solution 1 for WorkbookSource.plus_23206
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:49.842205+00:00
-- url     : https://prove2.me/submissions/67459370-3ab6-4553-82dc-331c53067e5b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b * (a + b) / (2 * a * b + a * c + b * c) + a * c * (a + c) / (2 * a * c + a * b + b * c) + b * c * (b + c) / (2 * b * c + a * c + a * b)) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + b * c)) / (4 * (a + b + c))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b^3 + a^5*b^2*c + a^5*b*c^2 + 2*a^5*c^3 - 2*a^4*b^4 - 6*a^4*b^2*c^2 - 2*a^4*c^4 + 2*a^3*b^5 + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + 2*a^3*c^5 + a^2*b^5*c - 6*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + a^2*b*c^5 + a*b^5*c^2 + a*b^2*c^5 + 2*b^5*c^3 - 2*b^4*c^4 + 2*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^6 * (b - a)^2 + (16 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^6 * (c - b)^2 + (68 : ℝ) * a^5 * (b - a)^3 + (102 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (90 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (28 : ℝ) * a^5 * (c - b)^3 + (120 : ℝ) * a^4 * (b - a)^4 + (240 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (230 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (110 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (20 : ℝ) * a^4 * (c - b)^4 + (114 : ℝ) * a^3 * (b - a)^5 + (285 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (314 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (186 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (55 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^3 * (c - b)^5 + (62 : ℝ) * a^2 * (b - a)^6 + (186 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (239 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (168 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (62 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (9 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (18 : ℝ) * a^1 * (b - a)^7 + (63 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (95 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (80 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (37 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (7 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * (b - a)^8 + (8 : ℝ) * (b - a)^7 * (c - b)^1 + (14 : ℝ) * (b - a)^6 * (c - b)^2 + (14 : ℝ) * (b - a)^5 * (c - b)^3 + (8 : ℝ) * (b - a)^4 * (c - b)^4 + (2 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b^3 + a^5*b^2*c + a^5*b*c^2 + 2*a^5*c^3 - 2*a^4*b^4 - 6*a^4*b^2*c^2 - 2*a^4*c^4 + 2*a^3*b^5 + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + 2*a^3*c^5 + a^2*b^5*c - 6*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + a^2*b*c^5 + a*b^5*c^2 + a*b^2*c^5 + 2*b^5*c^3 - 2*b^4*c^4 + 2*b^3*c^5) := by
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
  have hn : 0 ≤ (2*a^5*b^3 + a^5*b^2*c + a^5*b*c^2 + 2*a^5*c^3 - 2*a^4*b^4 - 6*a^4*b^2*c^2 - 2*a^4*c^4 + 2*a^3*b^5 + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + 2*a^3*c^5 + a^2*b^5*c - 6*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + a^2*b*c^5 + a*b^5*c^2 + a*b^2*c^5 + 2*b^5*c^3 - 2*b^4*c^4 + 2*b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b * (a + b) / (2 * a * b + a * c + b * c) + a * c * (a + c) / (2 * a * c + a * b + b * c) + b * c * (b + c) / (2 * b * c + a * c + a * b)) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + b * c)) / (4 * (a + b + c))) := @solution
#print axioms solution
