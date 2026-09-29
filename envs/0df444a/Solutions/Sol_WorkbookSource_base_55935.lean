-- Prove2me | solution 1 for WorkbookSource.base_55935
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:45.261612+00:00
-- url     : https://prove2.me/submissions/04371ad2-6165-48ca-9ed3-5c8cfa82ee34

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * (a * b + b * c + c * a) - 9 * a * b * c / (a + b + c)) * (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2)) ≥ 9 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6*b + 4*a^6*c - 5*a^5*b^2 - 6*a^5*b*c - 5*a^5*c^2 + 3*a^4*b^3 + 7*a^4*b^2*c + 7*a^4*b*c^2 + 3*a^4*c^3 + 3*a^3*b^4 - 18*a^3*b^3*c + 6*a^3*b^2*c^2 - 18*a^3*b*c^3 + 3*a^3*c^4 - 5*a^2*b^5 + 7*a^2*b^4*c + 6*a^2*b^3*c^2 + 6*a^2*b^2*c^3 + 7*a^2*b*c^4 - 5*a^2*c^5 + 4*a*b^6 - 6*a*b^5*c + 7*a*b^4*c^2 - 18*a*b^3*c^3 + 7*a*b^2*c^4 - 6*a*b*c^5 + 4*a*c^6 + 4*b^6*c - 5*b^5*c^2 + 3*b^4*c^3 + 3*b^3*c^4 - 5*b^2*c^5 + 4*b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^5 * (b - a)^2 + (24 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^5 * (c - b)^2 + (64 : ℝ) * a^4 * (b - a)^3 + (96 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (144 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (56 : ℝ) * a^4 * (c - b)^3 + (76 : ℝ) * a^3 * (b - a)^4 + (152 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (308 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (232 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (60 : ℝ) * a^3 * (c - b)^4 + (52 : ℝ) * a^2 * (b - a)^5 + (130 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (316 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (344 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (170 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (32 : ℝ) * a^2 * (c - b)^5 + (20 : ℝ) * a^1 * (b - a)^6 + (60 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (155 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (210 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (151 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (56 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (8 : ℝ) * a^1 * (c - b)^6 + (4 : ℝ) * (b - a)^7 + (14 : ℝ) * (b - a)^6 * (c - b)^1 + (32 : ℝ) * (b - a)^5 * (c - b)^2 + (45 : ℝ) * (b - a)^4 * (c - b)^3 + (38 : ℝ) * (b - a)^3 * (c - b)^4 + (19 : ℝ) * (b - a)^2 * (c - b)^5 + (4 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6*b + 4*a^6*c - 5*a^5*b^2 - 6*a^5*b*c - 5*a^5*c^2 + 3*a^4*b^3 + 7*a^4*b^2*c + 7*a^4*b*c^2 + 3*a^4*c^3 + 3*a^3*b^4 - 18*a^3*b^3*c + 6*a^3*b^2*c^2 - 18*a^3*b*c^3 + 3*a^3*c^4 - 5*a^2*b^5 + 7*a^2*b^4*c + 6*a^2*b^3*c^2 + 6*a^2*b^2*c^3 + 7*a^2*b*c^4 - 5*a^2*c^5 + 4*a*b^6 - 6*a*b^5*c + 7*a*b^4*c^2 - 18*a*b^3*c^3 + 7*a*b^2*c^4 - 6*a*b*c^5 + 4*a*c^6 + 4*b^6*c - 5*b^5*c^2 + 3*b^4*c^3 + 3*b^3*c^4 - 5*b^2*c^5 + 4*b*c^6) := by
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
  have hn : 0 ≤ (4*a^6*b + 4*a^6*c - 5*a^5*b^2 - 6*a^5*b*c - 5*a^5*c^2 + 3*a^4*b^3 + 7*a^4*b^2*c + 7*a^4*b*c^2 + 3*a^4*c^3 + 3*a^3*b^4 - 18*a^3*b^3*c + 6*a^3*b^2*c^2 - 18*a^3*b*c^3 + 3*a^3*c^4 - 5*a^2*b^5 + 7*a^2*b^4*c + 6*a^2*b^3*c^2 + 6*a^2*b^2*c^3 + 7*a^2*b*c^4 - 5*a^2*c^5 + 4*a*b^6 - 6*a*b^5*c + 7*a*b^4*c^2 - 18*a*b^3*c^3 + 7*a*b^2*c^4 - 6*a*b*c^5 + 4*a*c^6 + 4*b^6*c - 5*b^5*c^2 + 3*b^4*c^3 + 3*b^3*c^4 - 5*b^2*c^5 + 4*b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (2 * (a * b + b * c + c * a) - 9 * a * b * c / (a + b + c)) * (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2)) ≥ 9 / 2) := @solution
#print axioms solution
