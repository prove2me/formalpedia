-- Prove2me | solution 1 for WorkbookSource.plus_55303
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:42:10.9051+00:00
-- url     : https://prove2.me/submissions/8213799f-2518-4610-baee-17bccaec10e2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 / b + b^2 / c + c^2 / a) ≥ (2 * a^2 + b) / (b + c + 1) + (2 * b^2 + c) / (c + a + 1) + (2 * c^2 + a) / (a + b + 1)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (16*a^6*c/27 - 16*a^5*b*c/27 + 28*a^5*c^2/9 + 16*a^4*b^3/27 - 73*a^4*b^2*c/27 + 29*a^4*b*c^2/27 + 28*a^4*c^3/9 + 28*a^3*b^4/9 - 5*a^3*b^3*c/27 - 5*a^3*b^2*c^2 - 5*a^3*b*c^3/27 + 16*a^3*c^4/27 + 28*a^2*b^5/9 + 29*a^2*b^4*c/27 - 5*a^2*b^3*c^2 - 5*a^2*b^2*c^3 - 73*a^2*b*c^4/27 + 16*a*b^6/27 - 16*a*b^5*c/27 - 73*a*b^4*c^2/27 - 5*a*b^3*c^3/27 + 29*a*b^2*c^4/27 - 16*a*b*c^5/27 + 16*b^4*c^3/27 + 28*b^3*c^4/9 + 28*b^2*c^5/9 + 16*b*c^6/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (33 : ℝ) * a^5 * (b - a)^2 + (33 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (33 : ℝ) * a^5 * (c - b)^2 + (364/3 : ℝ) * a^4 * (b - a)^3 + (223 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (189 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (131/3 : ℝ) * a^4 * (c - b)^3 + (1610/9 : ℝ) * a^3 * (b - a)^4 + (4204/9 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (1432/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (1702/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (212/9 : ℝ) * a^3 * (c - b)^4 + (3580/27 : ℝ) * a^2 * (b - a)^5 + (11857/27 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (15046/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (8498/27 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (2057/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (164/27 : ℝ) * a^2 * (c - b)^5 + (445/9 : ℝ) * a^1 * (b - a)^6 + (1753/9 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (8086/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (5999/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (727/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (344/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (16/27 : ℝ) * a^1 * (c - b)^6 + (200/27 : ℝ) * (b - a)^7 + (100/3 : ℝ) * (b - a)^6 * (c - b)^1 + (544/9 : ℝ) * (b - a)^5 * (c - b)^2 + (56 : ℝ) * (b - a)^4 * (c - b)^3 + (248/9 : ℝ) * (b - a)^3 * (c - b)^4 + (20/3 : ℝ) * (b - a)^2 * (c - b)^5 + (16/27 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (16*a^6*c/27 - 16*a^5*b*c/27 + 28*a^5*c^2/9 + 16*a^4*b^3/27 - 73*a^4*b^2*c/27 + 29*a^4*b*c^2/27 + 28*a^4*c^3/9 + 28*a^3*b^4/9 - 5*a^3*b^3*c/27 - 5*a^3*b^2*c^2 - 5*a^3*b*c^3/27 + 16*a^3*c^4/27 + 28*a^2*b^5/9 + 29*a^2*b^4*c/27 - 5*a^2*b^3*c^2 - 5*a^2*b^2*c^3 - 73*a^2*b*c^4/27 + 16*a*b^6/27 - 16*a*b^5*c/27 - 73*a*b^4*c^2/27 - 5*a*b^3*c^3/27 + 29*a*b^2*c^4/27 - 16*a*b*c^5/27 + 16*b^4*c^3/27 + 28*b^3*c^4/9 + 28*b^2*c^5/9 + 16*b*c^6/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (33 : ℝ) * a^5 * (c - a)^2 + (33 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (33 : ℝ) * a^5 * (b - c)^2 + (364/3 : ℝ) * a^4 * (c - a)^3 + (141 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (107 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (131/3 : ℝ) * a^4 * (b - c)^3 + (1610/9 : ℝ) * a^3 * (c - a)^4 + (2236/9 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (448/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (718/9 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (212/9 : ℝ) * a^3 * (b - c)^4 + (3580/27 : ℝ) * a^2 * (c - a)^5 + (6043/27 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (3418/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (1298/27 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (671/27 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (164/27 : ℝ) * a^2 * (b - c)^5 + (445/9 : ℝ) * a^1 * (c - a)^6 + (917/9 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (1816/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (455/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (5 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (80/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (16/27 : ℝ) * a^1 * (b - c)^6 + (200/27 : ℝ) * (c - a)^7 + (500/27 : ℝ) * (c - a)^6 * (b - c)^1 + (16 : ℝ) * (c - a)^5 * (b - c)^2 + (148/27 : ℝ) * (c - a)^4 * (b - c)^3 + (16/27 : ℝ) * (c - a)^3 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (16*a^6*c/27 - 16*a^5*b*c/27 + 28*a^5*c^2/9 + 16*a^4*b^3/27 - 73*a^4*b^2*c/27 + 29*a^4*b*c^2/27 + 28*a^4*c^3/9 + 28*a^3*b^4/9 - 5*a^3*b^3*c/27 - 5*a^3*b^2*c^2 - 5*a^3*b*c^3/27 + 16*a^3*c^4/27 + 28*a^2*b^5/9 + 29*a^2*b^4*c/27 - 5*a^2*b^3*c^2 - 5*a^2*b^2*c^3 - 73*a^2*b*c^4/27 + 16*a*b^6/27 - 16*a*b^5*c/27 - 73*a*b^4*c^2/27 - 5*a*b^3*c^3/27 + 29*a*b^2*c^4/27 - 16*a*b*c^5/27 + 16*b^4*c^3/27 + 28*b^3*c^4/9 + 28*b^2*c^5/9 + 16*b*c^6/27) := by
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
  have he : (-a^5*b*c + a^5*c^2 + a^5*c - a^4*b^2*c - a^4*b*c + a^4*c^3 + 3*a^4*c^2 + 2*a^4*c + a^3*b^4 + a^3*b^3*c + a^3*b^3 - a^3*b^2*c^2 - 3*a^3*b^2*c + a^3*b*c^3 - a^3*b*c + a^3*c^3 + 2*a^3*c^2 + a^3*c + a^2*b^5 + 3*a^2*b^4 - a^2*b^3*c^2 + 2*a^2*b^3 - a^2*b^2*c^3 - 3*a^2*b^2*c^2 - 3*a^2*b^2*c - a^2*b*c^4 - 3*a^2*b*c^3 - 3*a^2*b*c^2 - a^2*b*c - a*b^5*c + a*b^5 - a*b^4*c^2 - a*b^4*c + 2*a*b^4 + a*b^3*c^3 - 3*a*b^3*c^2 - a*b^3*c + a*b^3 - 3*a*b^2*c^2 - a*b^2*c - a*b*c^5 - a*b*c^4 - a*b*c^3 - a*b*c^2 + b^3*c^4 + b^3*c^3 + b^2*c^5 + 3*b^2*c^4 + 2*b^2*c^3 + b*c^5 + 2*b*c^4 + b*c^3) = (16*a^6*c/27 - 16*a^5*b*c/27 + 28*a^5*c^2/9 + 16*a^4*b^3/27 - 73*a^4*b^2*c/27 + 29*a^4*b*c^2/27 + 28*a^4*c^3/9 + 28*a^3*b^4/9 - 5*a^3*b^3*c/27 - 5*a^3*b^2*c^2 - 5*a^3*b*c^3/27 + 16*a^3*c^4/27 + 28*a^2*b^5/9 + 29*a^2*b^4*c/27 - 5*a^2*b^3*c^2 - 5*a^2*b^2*c^3 - 73*a^2*b*c^4/27 + 16*a*b^6/27 - 16*a*b^5*c/27 - 73*a*b^4*c^2/27 - 5*a*b^3*c^3/27 + 29*a*b^2*c^4/27 - 16*a*b*c^5/27 + 16*b^4*c^3/27 + 28*b^3*c^4/9 + 28*b^2*c^5/9 + 16*b*c^6/27) := by
    linear_combination (-16*a^5*c/27 + 5*a^4*b*c/27 - 41*a^4*c^2/27 - 7*a^4*c/9 - 16*a^3*b^3/27 + 41*a^3*b^2*c/27 + 7*a^3*b*c^2/27 + a^3*b*c/3 - 16*a^3*c^3/27 - 7*a^3*c^2/9 - a^3*c/3 - 41*a^2*b^4/27 + 7*a^2*b^3*c/27 - 7*a^2*b^3/9 + 20*a^2*b^2*c^2/9 + 11*a^2*b^2*c/9 + 41*a^2*b*c^3/27 + 11*a^2*b*c^2/9 + a^2*b*c/3 - 16*a*b^5/27 + 5*a*b^4*c/27 - 7*a*b^4/9 + 41*a*b^3*c^2/27 + a*b^3*c/3 - a*b^3/3 + 7*a*b^2*c^3/27 + 11*a*b^2*c^2/9 + a*b^2*c/3 + 5*a*b*c^4/27 + a*b*c^3/3 + a*b*c^2/3 - 16*b^3*c^3/27 - 41*b^2*c^4/27 - 7*b^2*c^3/9 - 16*b*c^5/27 - 7*b*c^4/9 - b*c^3/3) * habc
  have hn : 0 ≤ (-a^5*b*c + a^5*c^2 + a^5*c - a^4*b^2*c - a^4*b*c + a^4*c^3 + 3*a^4*c^2 + 2*a^4*c + a^3*b^4 + a^3*b^3*c + a^3*b^3 - a^3*b^2*c^2 - 3*a^3*b^2*c + a^3*b*c^3 - a^3*b*c + a^3*c^3 + 2*a^3*c^2 + a^3*c + a^2*b^5 + 3*a^2*b^4 - a^2*b^3*c^2 + 2*a^2*b^3 - a^2*b^2*c^3 - 3*a^2*b^2*c^2 - 3*a^2*b^2*c - a^2*b*c^4 - 3*a^2*b*c^3 - 3*a^2*b*c^2 - a^2*b*c - a*b^5*c + a*b^5 - a*b^4*c^2 - a*b^4*c + 2*a*b^4 + a*b^3*c^3 - 3*a*b^3*c^2 - a*b^3*c + a*b^3 - 3*a*b^2*c^2 - a*b^2*c - a*b*c^5 - a*b*c^4 - a*b*c^3 - a*b*c^2 + b^3*c^4 + b^3*c^3 + b^2*c^5 + 3*b^2*c^4 + 2*b^2*c^3 + b*c^5 + 2*b*c^4 + b*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^2 / b + b^2 / c + c^2 / a) ≥ (2 * a^2 + b) / (b + c + 1) + (2 * b^2 + c) / (c + a + 1) + (2 * c^2 + a) / (a + b + 1)) := @solution
#print axioms solution
