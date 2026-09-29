-- Prove2me | solution 1 for WorkbookSource.base_3520
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:09:17.347925+00:00
-- url     : https://prove2.me/submissions/5097c3dd-0744-4d6a-8ccc-f1675268bbbf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * a^2 + b * c) + b^2 / (2 * b^2 + c * a) + c^2 / (2 * c^2 + a * b) + (a + b + c)^2 / (a * b + b * c + a * c)) ≥ 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6*b*c + 4*a^5*b^3 - 3*a^5*b^2*c - 3*a^5*b*c^2 + 4*a^5*c^3 - 4*a^4*b^4 - 2*a^4*b^3*c + 6*a^4*b^2*c^2 - 2*a^4*b*c^3 - 4*a^4*c^4 + 4*a^3*b^5 - 2*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 2*a^3*b*c^4 + 4*a^3*c^5 - 3*a^2*b^5*c + 6*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 6*a^2*b^2*c^4 - 3*a^2*b*c^5 + 2*a*b^6*c - 3*a*b^5*c^2 - 2*a*b^4*c^3 - 2*a*b^3*c^4 - 3*a*b^2*c^5 + 2*a*b*c^6 + 4*b^5*c^3 - 4*b^4*c^4 + 4*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (18 : ℝ) * a^6 * (b - a)^2 + (18 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (18 : ℝ) * a^6 * (c - b)^2 + (72 : ℝ) * a^5 * (b - a)^3 + (108 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (108 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (36 : ℝ) * a^5 * (c - b)^3 + (124 : ℝ) * a^4 * (b - a)^4 + (248 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (282 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (158 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (34 : ℝ) * a^4 * (c - b)^4 + (122 : ℝ) * a^3 * (b - a)^5 + (305 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (394 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (286 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (103 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (14 : ℝ) * a^3 * (c - b)^5 + (74 : ℝ) * a^2 * (b - a)^6 + (222 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (321 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (272 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (126 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (27 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^2 * (c - b)^6 + (26 : ℝ) * a^1 * (b - a)^7 + (91 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (147 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (140 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (77 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (21 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * (b - a)^8 + (16 : ℝ) * (b - a)^7 * (c - b)^1 + (28 : ℝ) * (b - a)^6 * (c - b)^2 + (28 : ℝ) * (b - a)^5 * (c - b)^3 + (16 : ℝ) * (b - a)^4 * (c - b)^4 + (4 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6*b*c + 4*a^5*b^3 - 3*a^5*b^2*c - 3*a^5*b*c^2 + 4*a^5*c^3 - 4*a^4*b^4 - 2*a^4*b^3*c + 6*a^4*b^2*c^2 - 2*a^4*b*c^3 - 4*a^4*c^4 + 4*a^3*b^5 - 2*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 2*a^3*b*c^4 + 4*a^3*c^5 - 3*a^2*b^5*c + 6*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 6*a^2*b^2*c^4 - 3*a^2*b*c^5 + 2*a*b^6*c - 3*a*b^5*c^2 - 2*a*b^4*c^3 - 2*a*b^3*c^4 - 3*a*b^2*c^5 + 2*a*b*c^6 + 4*b^5*c^3 - 4*b^4*c^4 + 4*b^3*c^5) := by
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
  have hn : 0 ≤ ((a^2 - a*b - a*c + b^2 - b*c + c^2)*(2*a^4*b*c + 4*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 4*a^3*c^3 - a^2*b^3*c + 6*a^2*b^2*c^2 - a^2*b*c^3 + 2*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4 + 4*b^3*c^3)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (2 * a^2 + b * c) + b^2 / (2 * b^2 + c * a) + c^2 / (2 * c^2 + a * b) + (a + b + c)^2 / (a * b + b * c + a * c)) ≥ 4) := @solution
#print axioms solution
