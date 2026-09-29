-- Prove2me | solution 1 for WorkbookSource.base_30484
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:19:12.293045+00:00
-- url     : https://prove2.me/submissions/b074f8da-7d8a-4d73-92ac-de1030845292

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (b + c) * (a / (2 * a + b + c)) + (b + c) / (c + a) * (b / (2 * b + c + a)) + (c + a) / (a + b) * (c / (2 * c + a + b)) ≤ 3 / 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^7*b + 2*a^7*c + 7*a^6*b^2 + 14*a^6*b*c + 11*a^6*c^2 + 12*a^5*b^3 + 16*a^5*b^2*c + 28*a^5*b*c^2 + 20*a^5*c^3 + 18*a^4*b^4 - 4*a^4*b^3*c - 36*a^4*b^2*c^2 + 12*a^4*b*c^3 + 18*a^4*c^4 + 20*a^3*b^5 + 12*a^3*b^4*c - 102*a^3*b^3*c^2 - 102*a^3*b^2*c^3 - 4*a^3*b*c^4 + 12*a^3*c^5 + 11*a^2*b^6 + 28*a^2*b^5*c - 36*a^2*b^4*c^2 - 102*a^2*b^3*c^3 - 36*a^2*b^2*c^4 + 16*a^2*b*c^5 + 7*a^2*c^6 + 2*a*b^7 + 14*a*b^6*c + 16*a*b^5*c^2 - 4*a*b^4*c^3 + 12*a*b^3*c^4 + 28*a*b^2*c^5 + 14*a*b*c^6 + 2*a*c^7 + 2*b^7*c + 7*b^6*c^2 + 12*b^5*c^3 + 18*b^4*c^4 + 20*b^3*c^5 + 11*b^2*c^6 + 2*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (768 : ℝ) * a^6 * (b - a)^2 + (768 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (768 : ℝ) * a^6 * (c - b)^2 + (3200 : ℝ) * a^5 * (b - a)^3 + (4968 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (4584 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (1408 : ℝ) * a^5 * (c - b)^3 + (5488 : ℝ) * a^4 * (b - a)^4 + (11536 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (11864 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (5816 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (1008 : ℝ) * a^4 * (c - b)^4 + (4960 : ℝ) * a^3 * (b - a)^5 + (13126 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (15756 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (9948 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (3062 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (352 : ℝ) * a^3 * (c - b)^5 + (2492 : ℝ) * a^2 * (b - a)^6 + (7932 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (11117 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (8490 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (3563 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (750 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (60 : ℝ) * a^2 * (c - b)^6 + (660 : ℝ) * a^1 * (b - a)^7 + (2448 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (3956 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (3544 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (1844 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (538 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (78 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * a^1 * (c - b)^7 + (72 : ℝ) * (b - a)^8 + (304 : ℝ) * (b - a)^7 * (c - b)^1 + (558 : ℝ) * (b - a)^6 * (c - b)^2 + (574 : ℝ) * (b - a)^5 * (c - b)^3 + (353 : ℝ) * (b - a)^4 * (c - b)^4 + (128 : ℝ) * (b - a)^3 * (c - b)^5 + (25 : ℝ) * (b - a)^2 * (c - b)^6 + (2 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^7*b + 2*a^7*c + 7*a^6*b^2 + 14*a^6*b*c + 11*a^6*c^2 + 12*a^5*b^3 + 16*a^5*b^2*c + 28*a^5*b*c^2 + 20*a^5*c^3 + 18*a^4*b^4 - 4*a^4*b^3*c - 36*a^4*b^2*c^2 + 12*a^4*b*c^3 + 18*a^4*c^4 + 20*a^3*b^5 + 12*a^3*b^4*c - 102*a^3*b^3*c^2 - 102*a^3*b^2*c^3 - 4*a^3*b*c^4 + 12*a^3*c^5 + 11*a^2*b^6 + 28*a^2*b^5*c - 36*a^2*b^4*c^2 - 102*a^2*b^3*c^3 - 36*a^2*b^2*c^4 + 16*a^2*b*c^5 + 7*a^2*c^6 + 2*a*b^7 + 14*a*b^6*c + 16*a*b^5*c^2 - 4*a*b^4*c^3 + 12*a*b^3*c^4 + 28*a*b^2*c^5 + 14*a*b*c^6 + 2*a*c^7 + 2*b^7*c + 7*b^6*c^2 + 12*b^5*c^3 + 18*b^4*c^4 + 20*b^3*c^5 + 11*b^2*c^6 + 2*b*c^7) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (768 : ℝ) * a^6 * (c - a)^2 + (768 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (768 : ℝ) * a^6 * (b - c)^2 + (3200 : ℝ) * a^5 * (c - a)^3 + (4632 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (4248 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (1408 : ℝ) * a^5 * (b - c)^3 + (5488 : ℝ) * a^4 * (c - a)^4 + (10416 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (10184 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (5256 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (1008 : ℝ) * a^4 * (b - c)^4 + (4960 : ℝ) * a^3 * (c - a)^5 + (11674 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (12852 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (8164 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (2730 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (352 : ℝ) * a^3 * (b - c)^5 + (2492 : ℝ) * a^2 * (c - a)^6 + (7020 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (8837 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (6498 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (2855 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (666 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (60 : ℝ) * a^2 * (b - c)^6 + (660 : ℝ) * a^1 * (c - a)^7 + (2172 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (3128 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (2616 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (1368 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (430 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (70 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (4 : ℝ) * a^1 * (b - c)^7 + (72 : ℝ) * (c - a)^8 + (272 : ℝ) * (c - a)^7 * (b - c)^1 + (446 : ℝ) * (c - a)^6 * (b - c)^2 + (422 : ℝ) * (c - a)^5 * (b - c)^3 + (253 : ℝ) * (c - a)^4 * (b - c)^4 + (96 : ℝ) * (c - a)^3 * (b - c)^5 + (21 : ℝ) * (c - a)^2 * (b - c)^6 + (2 : ℝ) * (c - a)^1 * (b - c)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^7*b + 2*a^7*c + 7*a^6*b^2 + 14*a^6*b*c + 11*a^6*c^2 + 12*a^5*b^3 + 16*a^5*b^2*c + 28*a^5*b*c^2 + 20*a^5*c^3 + 18*a^4*b^4 - 4*a^4*b^3*c - 36*a^4*b^2*c^2 + 12*a^4*b*c^3 + 18*a^4*c^4 + 20*a^3*b^5 + 12*a^3*b^4*c - 102*a^3*b^3*c^2 - 102*a^3*b^2*c^3 - 4*a^3*b*c^4 + 12*a^3*c^5 + 11*a^2*b^6 + 28*a^2*b^5*c - 36*a^2*b^4*c^2 - 102*a^2*b^3*c^3 - 36*a^2*b^2*c^4 + 16*a^2*b*c^5 + 7*a^2*c^6 + 2*a*b^7 + 14*a*b^6*c + 16*a*b^5*c^2 - 4*a*b^4*c^3 + 12*a*b^3*c^4 + 28*a*b^2*c^5 + 14*a*b*c^6 + 2*a*c^7 + 2*b^7*c + 7*b^6*c^2 + 12*b^5*c^3 + 18*b^4*c^4 + 20*b^3*c^5 + 11*b^2*c^6 + 2*b*c^7) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (2*a^7*b + 2*a^7*c + 7*a^6*b^2 + 14*a^6*b*c + 11*a^6*c^2 + 12*a^5*b^3 + 16*a^5*b^2*c + 28*a^5*b*c^2 + 20*a^5*c^3 + 18*a^4*b^4 - 4*a^4*b^3*c - 36*a^4*b^2*c^2 + 12*a^4*b*c^3 + 18*a^4*c^4 + 20*a^3*b^5 + 12*a^3*b^4*c - 102*a^3*b^3*c^2 - 102*a^3*b^2*c^3 - 4*a^3*b*c^4 + 12*a^3*c^5 + 11*a^2*b^6 + 28*a^2*b^5*c - 36*a^2*b^4*c^2 - 102*a^2*b^3*c^3 - 36*a^2*b^2*c^4 + 16*a^2*b*c^5 + 7*a^2*c^6 + 2*a*b^7 + 14*a*b^6*c + 16*a*b^5*c^2 - 4*a*b^4*c^3 + 12*a*b^3*c^4 + 28*a*b^2*c^5 + 14*a*b*c^6 + 2*a*c^7 + 2*b^7*c + 7*b^6*c^2 + 12*b^5*c^3 + 18*b^4*c^4 + 20*b^3*c^5 + 11*b^2*c^6 + 2*b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (b + c) * (a / (2 * a + b + c)) + (b + c) / (c + a) * (b / (2 * b + c + a)) + (c + a) / (a + b) * (c / (2 * c + a + b)) ≤ 3 / 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)) := @solution
#print axioms solution
