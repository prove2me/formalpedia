-- Prove2me | solution 1 for WorkbookSource.base_5408
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:38.457547+00:00
-- url     : https://prove2.me/submissions/96fa82f4-b8ed-4142-9414-a44307aceda5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^2 * (b + 1) / (a + b + a * b) + b^2 * (c + 1) / (b + c + b * c) + c^2 * (a + 1) / (c + a + c * a) ≥ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b/81 + a^6*c/81 + 5*a^5*b^2/81 + 10*a^5*b*c/81 + 5*a^5*c^2/81 + 10*a^4*b^3/81 + 13*a^4*b^2*c/81 + 13*a^4*b*c^2/81 + 10*a^4*c^3/81 + 10*a^3*b^4/81 + 8*a^3*b^3*c/81 - 76*a^3*b^2*c^2/81 + 8*a^3*b*c^3/81 + 10*a^3*c^4/81 + 5*a^2*b^5/81 + 13*a^2*b^4*c/81 - 76*a^2*b^3*c^2/81 - 76*a^2*b^2*c^3/81 + 13*a^2*b*c^4/81 + 5*a^2*c^5/81 + a*b^6/81 + 10*a*b^5*c/81 + 13*a*b^4*c^2/81 + 8*a*b^3*c^3/81 + 13*a*b^2*c^4/81 + 10*a*b*c^5/81 + a*c^6/81 + b^6*c/81 + 5*b^5*c^2/81 + 10*b^4*c^3/81 + 10*b^3*c^4/81 + 5*b^2*c^5/81 + b*c^6/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (10/3 : ℝ) * a^5 * (b - a)^2 + (10/3 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (10/3 : ℝ) * a^5 * (c - b)^2 + (322/27 : ℝ) * a^4 * (b - a)^3 + (161/9 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (139/9 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (128/27 : ℝ) * a^4 * (c - b)^3 + (1340/81 : ℝ) * a^3 * (b - a)^4 + (2680/81 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (820/27 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (1120/81 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (176/81 : ℝ) * a^3 * (c - b)^4 + (892/81 : ℝ) * a^2 * (b - a)^5 + (2230/81 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (2344/81 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (1286/81 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (344/81 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (32/81 : ℝ) * a^2 * (c - b)^5 + (280/81 : ℝ) * a^1 * (b - a)^6 + (280/27 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (1030/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (220/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (76/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (38/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (2/81 : ℝ) * a^1 * (c - b)^6 + (32/81 : ℝ) * (b - a)^7 + (112/81 : ℝ) * (b - a)^6 * (c - b)^1 + (160/81 : ℝ) * (b - a)^5 * (c - b)^2 + (40/27 : ℝ) * (b - a)^4 * (c - b)^3 + (50/81 : ℝ) * (b - a)^3 * (c - b)^4 + (11/81 : ℝ) * (b - a)^2 * (c - b)^5 + (1/81 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b/81 + a^6*c/81 + 5*a^5*b^2/81 + 10*a^5*b*c/81 + 5*a^5*c^2/81 + 10*a^4*b^3/81 + 13*a^4*b^2*c/81 + 13*a^4*b*c^2/81 + 10*a^4*c^3/81 + 10*a^3*b^4/81 + 8*a^3*b^3*c/81 - 76*a^3*b^2*c^2/81 + 8*a^3*b*c^3/81 + 10*a^3*c^4/81 + 5*a^2*b^5/81 + 13*a^2*b^4*c/81 - 76*a^2*b^3*c^2/81 - 76*a^2*b^2*c^3/81 + 13*a^2*b*c^4/81 + 5*a^2*c^5/81 + a*b^6/81 + 10*a*b^5*c/81 + 13*a*b^4*c^2/81 + 8*a*b^3*c^3/81 + 13*a*b^2*c^4/81 + 10*a*b*c^5/81 + a*c^6/81 + b^6*c/81 + 5*b^5*c^2/81 + 10*b^4*c^3/81 + 10*b^3*c^4/81 + 5*b^2*c^5/81 + b*c^6/81) := by
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
  have he : (a^3*b^2*c^2 + 2*a^3*b^2*c + a^3*b^2 + 2*a^3*b*c^2 + 3*a^3*b*c + a^3*b + a^3*c^2 + a^3*c + a^2*b^3*c^2 + 2*a^2*b^3*c + a^2*b^3 + a^2*b^2*c^3 + a^2*b^2*c^2 - a^2*b^2*c - a^2*b^2 + 2*a^2*b*c^3 - a^2*b*c^2 - 5*a^2*b*c - 2*a^2*b + a^2*c^3 - a^2*c^2 - 2*a^2*c + 2*a*b^3*c^2 + 3*a*b^3*c + a*b^3 + 2*a*b^2*c^3 - a*b^2*c^2 - 5*a*b^2*c - 2*a*b^2 + 3*a*b*c^3 - 5*a*b*c^2 - 4*a*b*c + a*c^3 - 2*a*c^2 + b^3*c^2 + b^3*c + b^2*c^3 - b^2*c^2 - 2*b^2*c + b*c^3 - 2*b*c^2) = (a^6*b/81 + a^6*c/81 + 5*a^5*b^2/81 + 10*a^5*b*c/81 + 5*a^5*c^2/81 + 10*a^4*b^3/81 + 13*a^4*b^2*c/81 + 13*a^4*b*c^2/81 + 10*a^4*c^3/81 + 10*a^3*b^4/81 + 8*a^3*b^3*c/81 - 76*a^3*b^2*c^2/81 + 8*a^3*b*c^3/81 + 10*a^3*c^4/81 + 5*a^2*b^5/81 + 13*a^2*b^4*c/81 - 76*a^2*b^3*c^2/81 - 76*a^2*b^2*c^3/81 + 13*a^2*b*c^4/81 + 5*a^2*c^5/81 + a*b^6/81 + 10*a*b^5*c/81 + 13*a*b^4*c^2/81 + 8*a*b^3*c^3/81 + 13*a*b^2*c^4/81 + 10*a*b*c^5/81 + a*c^6/81 + b^6*c/81 + 5*b^5*c^2/81 + 10*b^4*c^3/81 + 10*b^3*c^4/81 + 5*b^2*c^5/81 + b*c^6/81) := by
    linear_combination (-a^5*b/81 - a^5*c/81 - 4*a^4*b^2/81 - 8*a^4*b*c/81 - a^4*b/27 - 4*a^4*c^2/81 - a^4*c/27 - 2*a^3*b^3/27 - a^3*b^2*c/81 - a^3*b^2/9 - a^3*b*c^2/81 - 2*a^3*b*c/9 - a^3*b/9 - 2*a^3*c^3/27 - a^3*c^2/9 - a^3*c/9 - 4*a^2*b^4/81 - a^2*b^3*c/81 - a^2*b^3/9 + 53*a^2*b^2*c^2/27 + 62*a^2*b^2*c/27 + 7*a^2*b^2/9 - a^2*b*c^3/81 + 62*a^2*b*c^2/27 + 23*a^2*b*c/9 + 2*a^2*b/3 - 4*a^2*c^4/81 - a^2*c^3/9 + 7*a^2*c^2/9 + 2*a^2*c/3 - a*b^5/81 - 8*a*b^4*c/81 - a*b^4/27 - a*b^3*c^2/81 - 2*a*b^3*c/9 - a*b^3/9 - a*b^2*c^3/81 + 62*a*b^2*c^2/27 + 23*a*b^2*c/9 + 2*a*b^2/3 - 8*a*b*c^4/81 - 2*a*b*c^3/9 + 23*a*b*c^2/9 + 4*a*b*c/3 - a*c^5/81 - a*c^4/27 - a*c^3/9 + 2*a*c^2/3 - b^5*c/81 - 4*b^4*c^2/81 - b^4*c/27 - 2*b^3*c^3/27 - b^3*c^2/9 - b^3*c/9 - 4*b^2*c^4/81 - b^2*c^3/9 + 7*b^2*c^2/9 + 2*b^2*c/3 - b*c^5/81 - b*c^4/27 - b*c^3/9 + 2*b*c^2/3) * hab
  have hn : 0 ≤ (a^3*b^2*c^2 + 2*a^3*b^2*c + a^3*b^2 + 2*a^3*b*c^2 + 3*a^3*b*c + a^3*b + a^3*c^2 + a^3*c + a^2*b^3*c^2 + 2*a^2*b^3*c + a^2*b^3 + a^2*b^2*c^3 + a^2*b^2*c^2 - a^2*b^2*c - a^2*b^2 + 2*a^2*b*c^3 - a^2*b*c^2 - 5*a^2*b*c - 2*a^2*b + a^2*c^3 - a^2*c^2 - 2*a^2*c + 2*a*b^3*c^2 + 3*a*b^3*c + a*b^3 + 2*a*b^2*c^3 - a*b^2*c^2 - 5*a*b^2*c - 2*a*b^2 + 3*a*b*c^3 - 5*a*b*c^2 - 4*a*b*c + a*c^3 - 2*a*c^2 + b^3*c^2 + b^3*c + b^2*c^3 - b^2*c^2 - 2*b^2*c + b*c^3 - 2*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a^2 * (b + 1) / (a + b + a * b) + b^2 * (c + 1) / (b + c + b * c) + c^2 * (a + 1) / (c + a + c * a) ≥ 2) := @solution
#print axioms solution
