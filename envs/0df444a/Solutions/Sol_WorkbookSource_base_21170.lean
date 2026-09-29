-- Prove2me | solution 1 for WorkbookSource.base_21170
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:08.699452+00:00
-- url     : https://prove2.me/submissions/c3b2d8f2-65eb-42db-9074-2215550540e6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b ^ 2 / (a ^ 2 + 2 * b ^ 2 + c ^ 2) + b * c ^ 2 / (b ^ 2 + 2 * c ^ 2 + a ^ 2) + c * a ^ 2 / (c ^ 2 + 2 * a ^ 2 + b ^ 2)) ≤ (a + b + c) / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^7 + 2*a^6*b - 2*a^6*c - a^5*b^2 + 7*a^5*c^2 + 7*a^4*b^3 - 5*a^4*b^2*c - a^4*b*c^2 - 5*a^4*c^3 - 5*a^3*b^4 - 4*a^3*b^2*c^2 + 7*a^3*c^4 + 7*a^2*b^5 - a^2*b^4*c - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 - 5*a^2*b*c^4 - a^2*c^5 - 2*a*b^6 - 5*a*b^4*c^2 - a*b^2*c^4 + 2*a*c^6 + 2*b^7 + 2*b^6*c - b^5*c^2 + 7*b^4*c^3 - 5*b^3*c^4 + 7*b^2*c^5 - 2*b*c^6 + 2*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * a^5 * (b - a)^2 + (64 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (64 : ℝ) * a^5 * (c - b)^2 + (208 : ℝ) * a^4 * (b - a)^3 + (312 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (328 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (112 : ℝ) * a^4 * (c - b)^3 + (288 : ℝ) * a^3 * (b - a)^4 + (576 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (704 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (416 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (96 : ℝ) * a^3 * (c - b)^4 + (208 : ℝ) * a^2 * (b - a)^5 + (514 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (740 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (596 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (258 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (48 : ℝ) * a^2 * (c - b)^5 + (78 : ℝ) * a^1 * (b - a)^6 + (226 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (379 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (384 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (239 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (86 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (14 : ℝ) * a^1 * (c - b)^6 + (12 : ℝ) * (b - a)^7 + (38 : ℝ) * (b - a)^6 * (c - b)^1 + (72 : ℝ) * (b - a)^5 * (c - b)^2 + (87 : ℝ) * (b - a)^4 * (c - b)^3 + (70 : ℝ) * (b - a)^3 * (c - b)^4 + (37 : ℝ) * (b - a)^2 * (c - b)^5 + (12 : ℝ) * (b - a)^1 * (c - b)^6 + (2 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^7 + 2*a^6*b - 2*a^6*c - a^5*b^2 + 7*a^5*c^2 + 7*a^4*b^3 - 5*a^4*b^2*c - a^4*b*c^2 - 5*a^4*c^3 - 5*a^3*b^4 - 4*a^3*b^2*c^2 + 7*a^3*c^4 + 7*a^2*b^5 - a^2*b^4*c - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 - 5*a^2*b*c^4 - a^2*c^5 - 2*a*b^6 - 5*a*b^4*c^2 - a*b^2*c^4 + 2*a*c^6 + 2*b^7 + 2*b^6*c - b^5*c^2 + 7*b^4*c^3 - 5*b^3*c^4 + 7*b^2*c^5 - 2*b*c^6 + 2*c^7) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * a^5 * (c - a)^2 + (64 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (64 : ℝ) * a^5 * (b - c)^2 + (208 : ℝ) * a^4 * (c - a)^3 + (312 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (328 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (112 : ℝ) * a^4 * (b - c)^3 + (288 : ℝ) * a^3 * (c - a)^4 + (576 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (704 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (416 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (96 : ℝ) * a^3 * (b - c)^4 + (208 : ℝ) * a^2 * (c - a)^5 + (526 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (764 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (620 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (270 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (48 : ℝ) * a^2 * (b - c)^5 + (78 : ℝ) * a^1 * (c - a)^6 + (242 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (419 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (432 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (271 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (94 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (14 : ℝ) * a^1 * (b - c)^6 + (12 : ℝ) * (c - a)^7 + (46 : ℝ) * (c - a)^6 * (b - c)^1 + (96 : ℝ) * (c - a)^5 * (b - c)^2 + (123 : ℝ) * (c - a)^4 * (b - c)^3 + (102 : ℝ) * (c - a)^3 * (b - c)^4 + (53 : ℝ) * (c - a)^2 * (b - c)^5 + (16 : ℝ) * (c - a)^1 * (b - c)^6 + (2 : ℝ) * (b - c)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^7 + 2*a^6*b - 2*a^6*c - a^5*b^2 + 7*a^5*c^2 + 7*a^4*b^3 - 5*a^4*b^2*c - a^4*b*c^2 - 5*a^4*c^3 - 5*a^3*b^4 - 4*a^3*b^2*c^2 + 7*a^3*c^4 + 7*a^2*b^5 - a^2*b^4*c - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 - 5*a^2*b*c^4 - a^2*c^5 - 2*a*b^6 - 5*a*b^4*c^2 - a*b^2*c^4 + 2*a*c^6 + 2*b^7 + 2*b^6*c - b^5*c^2 + 7*b^4*c^3 - 5*b^3*c^4 + 7*b^2*c^5 - 2*b*c^6 + 2*c^7) := by
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
  have hn : 0 ≤ (2*a^7 + 2*a^6*b - 2*a^6*c - a^5*b^2 + 7*a^5*c^2 + 7*a^4*b^3 - 5*a^4*b^2*c - a^4*b*c^2 - 5*a^4*c^3 - 5*a^3*b^4 - 4*a^3*b^2*c^2 + 7*a^3*c^4 + 7*a^2*b^5 - a^2*b^4*c - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 - 5*a^2*b*c^4 - a^2*c^5 - 2*a*b^6 - 5*a*b^4*c^2 - a*b^2*c^4 + 2*a*c^6 + 2*b^7 + 2*b^6*c - b^5*c^2 + 7*b^4*c^3 - 5*b^3*c^4 + 7*b^2*c^5 - 2*b*c^6 + 2*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b ^ 2 / (a ^ 2 + 2 * b ^ 2 + c ^ 2) + b * c ^ 2 / (b ^ 2 + 2 * c ^ 2 + a ^ 2) + c * a ^ 2 / (c ^ 2 + 2 * a ^ 2 + b ^ 2)) ≤ (a + b + c) / 4) := @solution
#print axioms solution
