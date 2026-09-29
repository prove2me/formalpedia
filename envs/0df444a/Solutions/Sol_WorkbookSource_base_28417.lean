-- Prove2me | solution 1 for WorkbookSource.base_28417
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:01:50.119562+00:00
-- url     : https://prove2.me/submissions/bb7e1d56-6580-4ed7-a5cc-bc88d24a4261

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 3 * b + 3 * c) ^ 2 / (37 * a ^ 2 + 3 * (b + c) ^ 2) + (b + 3 * c + 3 * a) ^ 2 / (37 * b ^ 2 + 3 * (c + a) ^ 2) + (c + 3 * a + 3 * b) ^ 2 / (37 * c ^ 2 + 3 * (a + b) ^ 2) ≥ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (1008*a^6 + 2736*a^5*b + 2736*a^5*c + 2832*a^4*b^2 + 5904*a^4*b*c + 2832*a^4*c^2 + 2208*a^3*b^3 + 13632*a^3*b^2*c + 13632*a^3*b*c^2 + 2208*a^3*c^3 + 2832*a^2*b^4 + 13632*a^2*b^3*c - 142560*a^2*b^2*c^2 + 13632*a^2*b*c^3 + 2832*a^2*c^4 + 2736*a*b^5 + 5904*a*b^4*c + 13632*a*b^3*c^2 + 13632*a*b^2*c^3 + 5904*a*b*c^4 + 2736*a*c^5 + 1008*b^6 + 2736*b^5*c + 2832*b^4*c^2 + 2208*b^3*c^3 + 2832*b^2*c^4 + 2736*b*c^5 + 1008*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (124656 : ℝ) * a^4 * (b - a)^2 + (124656 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (124656 : ℝ) * a^4 * (c - b)^2 + (345792 : ℝ) * a^3 * (b - a)^3 + (518688 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (478560 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (152832 : ℝ) * a^3 * (c - b)^3 + (343488 : ℝ) * a^2 * (b - a)^4 + (686976 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (680832 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (337344 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (54048 : ℝ) * a^2 * (c - b)^4 + (136704 : ℝ) * a^1 * (b - a)^5 + (341760 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (393024 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (247776 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (82848 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (11520 : ℝ) * a^1 * (c - b)^5 + (15360 : ℝ) * (b - a)^6 + (46080 : ℝ) * (b - a)^5 * (c - b)^1 + (68928 : ℝ) * (b - a)^4 * (c - b)^2 + (61056 : ℝ) * (b - a)^3 * (c - b)^3 + (31632 : ℝ) * (b - a)^2 * (c - b)^4 + (8784 : ℝ) * (b - a)^1 * (c - b)^5 + (1008 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (1008*a^6 + 2736*a^5*b + 2736*a^5*c + 2832*a^4*b^2 + 5904*a^4*b*c + 2832*a^4*c^2 + 2208*a^3*b^3 + 13632*a^3*b^2*c + 13632*a^3*b*c^2 + 2208*a^3*c^3 + 2832*a^2*b^4 + 13632*a^2*b^3*c - 142560*a^2*b^2*c^2 + 13632*a^2*b*c^3 + 2832*a^2*c^4 + 2736*a*b^5 + 5904*a*b^4*c + 13632*a*b^3*c^2 + 13632*a*b^2*c^3 + 5904*a*b*c^4 + 2736*a*c^5 + 1008*b^6 + 2736*b^5*c + 2832*b^4*c^2 + 2208*b^3*c^3 + 2832*b^2*c^4 + 2736*b*c^5 + 1008*c^6) := by
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
  have hn : 0 ≤ (1008*a^6 + 2736*a^5*b + 2736*a^5*c + 2832*a^4*b^2 + 5904*a^4*b*c + 2832*a^4*c^2 + 2208*a^3*b^3 + 13632*a^3*b^2*c + 13632*a^3*b*c^2 + 2208*a^3*c^3 + 2832*a^2*b^4 + 13632*a^2*b^3*c - 142560*a^2*b^2*c^2 + 13632*a^2*b*c^3 + 2832*a^2*c^4 + 2736*a*b^5 + 5904*a*b^4*c + 13632*a*b^3*c^2 + 13632*a*b^2*c^3 + 5904*a*b*c^4 + 2736*a*c^5 + 1008*b^6 + 2736*b^5*c + 2832*b^4*c^2 + 2208*b^3*c^3 + 2832*b^2*c^4 + 2736*b*c^5 + 1008*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + 3 * b + 3 * c) ^ 2 / (37 * a ^ 2 + 3 * (b + c) ^ 2) + (b + 3 * c + 3 * a) ^ 2 / (37 * b ^ 2 + 3 * (c + a) ^ 2) + (c + 3 * a + 3 * b) ^ 2 / (37 * c ^ 2 + 3 * (a + b) ^ 2) ≥ 3) := @solution
#print axioms solution
