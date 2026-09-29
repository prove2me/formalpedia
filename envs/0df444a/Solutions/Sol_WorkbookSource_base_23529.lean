-- Prove2me | solution 1 for WorkbookSource.base_23529
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:58:36.107617+00:00
-- url     : https://prove2.me/submissions/b98430c8-0d44-4983-891a-f7eea94dabfe

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (a^2 + b * c) + b^3 / (b^2 + c * a) + c^3 / (c^2 + a * b) ) ≥ (2 * (a^2 + b^2 + c^2) + a * b + b * c + c * a) / (2 * (a + b + c))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b^2*c + a^5*b*c^2 + 3*a^4*b^4 - a^4*b^3*c - 3*a^4*b^2*c^2 - a^4*b*c^3 + 3*a^4*c^4 - a^3*b^4*c - a^3*b*c^4 + a^2*b^5*c - 3*a^2*b^4*c^2 - 3*a^2*b^2*c^4 + a^2*b*c^5 + a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + a*b^2*c^5 + 3*b^4*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^6 * (b - a)^2 + (16 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^6 * (c - b)^2 + (74 : ℝ) * a^5 * (b - a)^3 + (111 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (81 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (22 : ℝ) * a^5 * (c - b)^3 + (141 : ℝ) * a^4 * (b - a)^4 + (282 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (218 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (77 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (11 : ℝ) * a^4 * (c - b)^4 + (142 : ℝ) * a^3 * (b - a)^5 + (355 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (330 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (140 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (27 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^3 * (c - b)^5 + (80 : ℝ) * a^2 * (b - a)^6 + (240 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (269 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (138 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (32 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (24 : ℝ) * a^1 * (b - a)^7 + (84 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (110 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (65 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (16 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (1 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (3 : ℝ) * (b - a)^8 + (12 : ℝ) * (b - a)^7 * (c - b)^1 + (18 : ℝ) * (b - a)^6 * (c - b)^2 + (12 : ℝ) * (b - a)^5 * (c - b)^3 + (3 : ℝ) * (b - a)^4 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b^2*c + a^5*b*c^2 + 3*a^4*b^4 - a^4*b^3*c - 3*a^4*b^2*c^2 - a^4*b*c^3 + 3*a^4*c^4 - a^3*b^4*c - a^3*b*c^4 + a^2*b^5*c - 3*a^2*b^4*c^2 - 3*a^2*b^2*c^4 + a^2*b*c^5 + a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + a*b^2*c^5 + 3*b^4*c^4) := by
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
  have hn : 0 ≤ (a^5*b^2*c + a^5*b*c^2 + 3*a^4*b^4 - a^4*b^3*c - 3*a^4*b^2*c^2 - a^4*b*c^3 + 3*a^4*c^4 - a^3*b^4*c - a^3*b*c^4 + a^2*b^5*c - 3*a^2*b^4*c^2 - 3*a^2*b^2*c^4 + a^2*b*c^5 + a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + a*b^2*c^5 + 3*b^4*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 / (a^2 + b * c) + b^3 / (b^2 + c * a) + c^3 / (c^2 + a * b) ) ≥ (2 * (a^2 + b^2 + c^2) + a * b + b * c + c * a) / (2 * (a + b + c))) := @solution
#print axioms solution
