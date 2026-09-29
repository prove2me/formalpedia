-- Prove2me | solution 1 for WorkbookSource.base_21189
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:09.413608+00:00
-- url     : https://prove2.me/submissions/74cff177-b558-4239-b274-c77d42509028

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 / 8 + a / (c + b) + b / (a + c) + c / (b + a) ≥ 25 / 8 * (a / (a + 2 * b + 2 * c) + b / (b + 2 * c + 2 * a) + c / (c + 2 * a + 2 * b))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (16*a^6 + 28*a^5*b + 28*a^5*c + 5*a^4*b^2 + 30*a^4*b*c + 5*a^4*c^2 - 14*a^3*b^3 - 36*a^3*b^2*c - 36*a^3*b*c^2 - 14*a^3*c^3 + 5*a^2*b^4 - 36*a^2*b^3*c - 78*a^2*b^2*c^2 - 36*a^2*b*c^3 + 5*a^2*c^4 + 28*a*b^5 + 30*a*b^4*c - 36*a*b^3*c^2 - 36*a*b^2*c^3 + 30*a*b*c^4 + 28*a*c^5 + 16*b^6 + 28*b^5*c + 5*b^4*c^2 - 14*b^3*c^3 + 5*b^2*c^4 + 28*b*c^5 + 16*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (600 : ℝ) * a^4 * (b - a)^2 + (600 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (600 : ℝ) * a^4 * (c - b)^2 + (1460 : ℝ) * a^3 * (b - a)^3 + (2190 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (2610 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (940 : ℝ) * a^3 * (c - b)^3 + (1340 : ℝ) * a^2 * (b - a)^4 + (2680 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (3870 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (2530 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (560 : ℝ) * a^2 * (c - b)^4 + (548 : ℝ) * a^1 * (b - a)^5 + (1370 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (2368 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (2182 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (940 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (152 : ℝ) * a^1 * (c - b)^5 + (84 : ℝ) * (b - a)^6 + (252 : ℝ) * (b - a)^5 * (c - b)^1 + (513 : ℝ) * (b - a)^4 * (c - b)^2 + (606 : ℝ) * (b - a)^3 * (c - b)^3 + (385 : ℝ) * (b - a)^2 * (c - b)^4 + (124 : ℝ) * (b - a)^1 * (c - b)^5 + (16 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (16*a^6 + 28*a^5*b + 28*a^5*c + 5*a^4*b^2 + 30*a^4*b*c + 5*a^4*c^2 - 14*a^3*b^3 - 36*a^3*b^2*c - 36*a^3*b*c^2 - 14*a^3*c^3 + 5*a^2*b^4 - 36*a^2*b^3*c - 78*a^2*b^2*c^2 - 36*a^2*b*c^3 + 5*a^2*c^4 + 28*a*b^5 + 30*a*b^4*c - 36*a*b^3*c^2 - 36*a*b^2*c^3 + 30*a*b*c^4 + 28*a*c^5 + 16*b^6 + 28*b^5*c + 5*b^4*c^2 - 14*b^3*c^3 + 5*b^2*c^4 + 28*b*c^5 + 16*c^6) := by
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
  have hn : 0 ≤ (16*a^6 + 28*a^5*b + 28*a^5*c + 5*a^4*b^2 + 30*a^4*b*c + 5*a^4*c^2 - 14*a^3*b^3 - 36*a^3*b^2*c - 36*a^3*b*c^2 - 14*a^3*c^3 + 5*a^2*b^4 - 36*a^2*b^3*c - 78*a^2*b^2*c^2 - 36*a^2*b*c^3 + 5*a^2*c^4 + 28*a*b^5 + 30*a*b^4*c - 36*a*b^3*c^2 - 36*a*b^2*c^3 + 30*a*b*c^4 + 28*a*c^5 + 16*b^6 + 28*b^5*c + 5*b^4*c^2 - 14*b^3*c^3 + 5*b^2*c^4 + 28*b*c^5 + 16*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 3 / 8 + a / (c + b) + b / (a + c) + c / (b + a) ≥ 25 / 8 * (a / (a + 2 * b + 2 * c) + b / (b + 2 * c + 2 * a) + c / (c + 2 * a + 2 * b))) := @solution
#print axioms solution
