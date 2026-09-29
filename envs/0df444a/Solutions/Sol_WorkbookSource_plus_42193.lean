-- Prove2me | solution 1 for WorkbookSource.plus_42193
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:09:07.837981+00:00
-- url     : https://prove2.me/submissions/0fa9fef8-ba2a-4c32-ab06-6353f5c31ea0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a + 2 * b + c) ^ 2 + 1 / (2 * b + 2 * c + a) ^ 2 + 1 / (2 * c + 2 * a + b) ^ 2) ≥ 27 / (25 * (a + b + c) ^ 2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (168*a^6 + 476*a^5*b + 476*a^5*c + 309*a^4*b^2 + 552*a^4*b*c + 309*a^4*c^2 + 2*a^3*b^3 - 782*a^3*b^2*c - 782*a^3*b*c^2 + 2*a^3*c^3 + 309*a^2*b^4 - 782*a^2*b^3*c - 2184*a^2*b^2*c^2 - 782*a^2*b*c^3 + 309*a^2*c^4 + 476*a*b^5 + 552*a*b^4*c - 782*a*b^3*c^2 - 782*a*b^2*c^3 + 552*a*b*c^4 + 476*a*c^5 + 168*b^6 + 476*b^5*c + 309*b^4*c^2 + 2*b^3*c^3 + 309*b^2*c^4 + 476*b*c^5 + 168*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (11250 : ℝ) * a^4 * (b - a)^2 + (11250 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (11250 : ℝ) * a^4 * (c - b)^2 + (29000 : ℝ) * a^3 * (b - a)^3 + (43500 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (46500 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (16000 : ℝ) * a^3 * (c - b)^3 + (27950 : ℝ) * a^2 * (b - a)^4 + (55900 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (68850 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (40900 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (8450 : ℝ) * a^2 * (c - b)^4 + (11940 : ℝ) * a^1 * (b - a)^5 + (29850 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (42740 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (34260 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (13350 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1960 : ℝ) * a^1 * (c - b)^5 + (1908 : ℝ) * (b - a)^6 + (5724 : ℝ) * (b - a)^5 * (c - b)^1 + (9449 : ℝ) * (b - a)^4 * (c - b)^2 + (9358 : ℝ) * (b - a)^3 * (c - b)^3 + (5209 : ℝ) * (b - a)^2 * (c - b)^4 + (1484 : ℝ) * (b - a)^1 * (c - b)^5 + (168 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (168*a^6 + 476*a^5*b + 476*a^5*c + 309*a^4*b^2 + 552*a^4*b*c + 309*a^4*c^2 + 2*a^3*b^3 - 782*a^3*b^2*c - 782*a^3*b*c^2 + 2*a^3*c^3 + 309*a^2*b^4 - 782*a^2*b^3*c - 2184*a^2*b^2*c^2 - 782*a^2*b*c^3 + 309*a^2*c^4 + 476*a*b^5 + 552*a*b^4*c - 782*a*b^3*c^2 - 782*a*b^2*c^3 + 552*a*b*c^4 + 476*a*c^5 + 168*b^6 + 476*b^5*c + 309*b^4*c^2 + 2*b^3*c^3 + 309*b^2*c^4 + 476*b*c^5 + 168*c^6) := by
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
  have hn : 0 ≤ (168*a^6 + 476*a^5*b + 476*a^5*c + 309*a^4*b^2 + 552*a^4*b*c + 309*a^4*c^2 + 2*a^3*b^3 - 782*a^3*b^2*c - 782*a^3*b*c^2 + 2*a^3*c^3 + 309*a^2*b^4 - 782*a^2*b^3*c - 2184*a^2*b^2*c^2 - 782*a^2*b*c^3 + 309*a^2*c^4 + 476*a*b^5 + 552*a*b^4*c - 782*a*b^3*c^2 - 782*a*b^2*c^3 + 552*a*b*c^4 + 476*a*c^5 + 168*b^6 + 476*b^5*c + 309*b^4*c^2 + 2*b^3*c^3 + 309*b^2*c^4 + 476*b*c^5 + 168*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (2 * a + 2 * b + c) ^ 2 + 1 / (2 * b + 2 * c + a) ^ 2 + 1 / (2 * c + 2 * a + b) ^ 2) ≥ 27 / (25 * (a + b + c) ^ 2)) := @solution
#print axioms solution
