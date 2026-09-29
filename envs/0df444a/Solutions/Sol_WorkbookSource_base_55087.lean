-- Prove2me | solution 1 for WorkbookSource.base_55087
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:30.146702+00:00
-- url     : https://prove2.me/submissions/301eb9f7-dc30-4a35-af70-20bfd506c4df

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 9 * (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 ≥ (a ^ 5 + b ^ 5 + c ^ 5) * (a + b + c) ^ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^8 - 3*a^7*b - 3*a^7*c - 3*a^6*b^2 - 6*a^6*b*c - 3*a^6*c^2 - a^5*b^3 - 3*a^5*b^2*c - 3*a^5*b*c^2 - a^5*c^3 + 18*a^4*b^4 + 18*a^4*c^4 - a^3*b^5 - a^3*c^5 - 3*a^2*b^6 - 3*a^2*b^5*c - 3*a^2*b*c^5 - 3*a^2*c^6 - 3*a*b^7 - 6*a*b^6*c - 3*a*b^5*c^2 - 3*a*b^2*c^5 - 6*a*b*c^6 - 3*a*c^7 + 8*b^8 - 3*b^7*c - 3*b^6*c^2 - b^5*c^3 + 18*b^4*c^4 - b^3*c^5 - 3*b^2*c^6 - 3*b*c^7 + 8*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^6 * (b - a)^2 + (36 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^6 * (c - b)^2 + (156 : ℝ) * a^5 * (b - a)^3 + (234 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (198 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (60 : ℝ) * a^5 * (c - b)^3 + (406 : ℝ) * a^4 * (b - a)^4 + (812 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (888 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (482 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (166 : ℝ) * a^4 * (c - b)^4 + (542 : ℝ) * a^3 * (b - a)^5 + (1355 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1990 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1630 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (937 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (242 : ℝ) * a^3 * (c - b)^5 + (380 : ℝ) * a^2 * (b - a)^6 + (1140 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (2115 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (2330 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (1848 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (873 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (170 : ℝ) * a^2 * (c - b)^6 + (136 : ℝ) * a^1 * (b - a)^7 + (476 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (1062 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (1465 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (1482 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (996 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (373 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (58 : ℝ) * a^1 * (c - b)^7 + (20 : ℝ) * (b - a)^8 + (80 : ℝ) * (b - a)^7 * (c - b)^1 + (208 : ℝ) * (b - a)^6 * (c - b)^2 + (344 : ℝ) * (b - a)^5 * (c - b)^3 + (423 : ℝ) * (b - a)^4 * (c - b)^4 + (366 : ℝ) * (b - a)^3 * (c - b)^5 + (200 : ℝ) * (b - a)^2 * (c - b)^6 + (61 : ℝ) * (b - a)^1 * (c - b)^7 + (8 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^8 - 3*a^7*b - 3*a^7*c - 3*a^6*b^2 - 6*a^6*b*c - 3*a^6*c^2 - a^5*b^3 - 3*a^5*b^2*c - 3*a^5*b*c^2 - a^5*c^3 + 18*a^4*b^4 + 18*a^4*c^4 - a^3*b^5 - a^3*c^5 - 3*a^2*b^6 - 3*a^2*b^5*c - 3*a^2*b*c^5 - 3*a^2*c^6 - 3*a*b^7 - 6*a*b^6*c - 3*a*b^5*c^2 - 3*a*b^2*c^5 - 6*a*b*c^6 - 3*a*c^7 + 8*b^8 - 3*b^7*c - 3*b^6*c^2 - b^5*c^3 + 18*b^4*c^4 - b^3*c^5 - 3*b^2*c^6 - 3*b*c^7 + 8*c^8) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), 9 * (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 ≥ (a ^ 5 + b ^ 5 + c ^ 5) * (a + b + c) ^ 3) := @solution
#print axioms solution
