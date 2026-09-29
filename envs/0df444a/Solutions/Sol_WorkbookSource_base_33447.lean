-- Prove2me | solution 1 for WorkbookSource.base_33447
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:30:14.591176+00:00
-- url     : https://prove2.me/submissions/8e8b4bab-c252-4294-9eb5-e2d7803e7d26

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a ^ 2 + 2 * b * c) + 1 / (b ^ 2 + 2 * c * a) + 1 / (c ^ 2 + 2 * a * b) ≤ 1 / 3 * (1 / (a * b) + 1 / (b * c) + 1 / (c * a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*b*c + 2*a^4*b^3 - 2*a^4*b^2*c - 2*a^4*b*c^2 + 2*a^4*c^3 + 2*a^3*b^4 - a^3*b^3*c - 3*a^3*b^2*c^2 - a^3*b*c^3 + 2*a^3*c^4 - 2*a^2*b^4*c - 3*a^2*b^3*c^2 - 3*a^2*b^2*c^3 - 2*a^2*b*c^4 + 4*a*b^5*c - 2*a*b^4*c^2 - a*b^3*c^3 - 2*a*b^2*c^4 + 4*a*b*c^5 + 2*b^4*c^3 + 2*b^3*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * a^5 * (b - a)^2 + (27 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (27 : ℝ) * a^5 * (c - b)^2 + (96 : ℝ) * a^4 * (b - a)^3 + (144 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (126 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (39 : ℝ) * a^4 * (c - b)^3 + (134 : ℝ) * a^3 * (b - a)^4 + (268 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (252 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (118 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (20 : ℝ) * a^3 * (c - b)^4 + (92 : ℝ) * a^2 * (b - a)^5 + (230 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (248 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (142 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (40 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^2 * (c - b)^5 + (31 : ℝ) * a^1 * (b - a)^6 + (93 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (113 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (71 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (24 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (4 : ℝ) * (b - a)^7 + (14 : ℝ) * (b - a)^6 * (c - b)^1 + (18 : ℝ) * (b - a)^5 * (c - b)^2 + (10 : ℝ) * (b - a)^4 * (c - b)^3 + (2 : ℝ) * (b - a)^3 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*b*c + 2*a^4*b^3 - 2*a^4*b^2*c - 2*a^4*b*c^2 + 2*a^4*c^3 + 2*a^3*b^4 - a^3*b^3*c - 3*a^3*b^2*c^2 - a^3*b*c^3 + 2*a^3*c^4 - 2*a^2*b^4*c - 3*a^2*b^3*c^2 - 3*a^2*b^2*c^3 - 2*a^2*b*c^4 + 4*a*b^5*c - 2*a*b^4*c^2 - a*b^3*c^3 - 2*a*b^2*c^4 + 4*a*b*c^5 + 2*b^4*c^3 + 2*b^3*c^4) := by
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
  have hn : 0 ≤ (4*a^5*b*c + 2*a^4*b^3 - 2*a^4*b^2*c - 2*a^4*b*c^2 + 2*a^4*c^3 + 2*a^3*b^4 - a^3*b^3*c - 3*a^3*b^2*c^2 - a^3*b*c^3 + 2*a^3*c^4 - 2*a^2*b^4*c - 3*a^2*b^3*c^2 - 3*a^2*b^2*c^3 - 2*a^2*b*c^4 + 4*a*b^5*c - 2*a*b^4*c^2 - a*b^3*c^3 - 2*a*b^2*c^4 + 4*a*b*c^5 + 2*b^4*c^3 + 2*b^3*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 1 / (a ^ 2 + 2 * b * c) + 1 / (b ^ 2 + 2 * c * a) + 1 / (c ^ 2 + 2 * a * b) ≤ 1 / 3 * (1 / (a * b) + 1 / (b * c) + 1 / (c * a))) := @solution
#print axioms solution
