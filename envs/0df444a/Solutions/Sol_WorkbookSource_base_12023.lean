-- Prove2me | solution 1 for WorkbookSource.base_12023
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:19.512596+00:00
-- url     : https://prove2.me/submissions/53249eaf-fc55-4ac0-a60a-453d963fac4b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^4 + b^4 + c^4)^2 ≥ (a^2 + b^2 + c^2) * (a^5 + b^5 + c^5)  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^8/3 - a^7*b/3 - a^7*c/3 - a^6*b^2/3 - a^6*c^2/3 - a^5*b^3/3 - a^5*b^2*c/3 - a^5*b*c^2/3 - a^5*c^3/3 + 2*a^4*b^4 + 2*a^4*c^4 - a^3*b^5/3 - a^3*c^5/3 - a^2*b^6/3 - a^2*b^5*c/3 - a^2*b*c^5/3 - a^2*c^6/3 - a*b^7/3 - a*b^5*c^2/3 - a*b^2*c^5/3 - a*c^7/3 + 2*b^8/3 - b^7*c/3 - b^6*c^2/3 - b^5*c^3/3 + 2*b^4*c^4 - b^3*c^5/3 - b^2*c^6/3 - b*c^7/3 + 2*c^8/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^6 * (b - a)^2 + (2 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^6 * (c - b)^2 + (28/3 : ℝ) * a^5 * (b - a)^3 + (14 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (10 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (8/3 : ℝ) * a^5 * (c - b)^3 + (82/3 : ℝ) * a^4 * (b - a)^4 + (164/3 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (166/3 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (28 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (32/3 : ℝ) * a^4 * (c - b)^4 + (38 : ℝ) * a^3 * (b - a)^5 + (95 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (410/3 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (110 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (199/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * a^3 * (c - b)^5 + (80/3 : ℝ) * a^2 * (b - a)^6 + (80 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (445/3 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (490/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (406/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (67 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (40/3 : ℝ) * a^2 * (c - b)^6 + (28/3 : ℝ) * a^1 * (b - a)^7 + (98/3 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (220/3 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (305/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (108 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (230/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (89/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (14/3 : ℝ) * a^1 * (c - b)^7 + (4/3 : ℝ) * (b - a)^8 + (16/3 : ℝ) * (b - a)^7 * (c - b)^1 + (14 : ℝ) * (b - a)^6 * (c - b)^2 + (70/3 : ℝ) * (b - a)^5 * (c - b)^3 + (91/3 : ℝ) * (b - a)^4 * (c - b)^4 + (28 : ℝ) * (b - a)^3 * (c - b)^5 + (16 : ℝ) * (b - a)^2 * (c - b)^6 + (5 : ℝ) * (b - a)^1 * (c - b)^7 + (2/3 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^8/3 - a^7*b/3 - a^7*c/3 - a^6*b^2/3 - a^6*c^2/3 - a^5*b^3/3 - a^5*b^2*c/3 - a^5*b*c^2/3 - a^5*c^3/3 + 2*a^4*b^4 + 2*a^4*c^4 - a^3*b^5/3 - a^3*c^5/3 - a^2*b^6/3 - a^2*b^5*c/3 - a^2*b*c^5/3 - a^2*c^6/3 - a*b^7/3 - a*b^5*c^2/3 - a*b^2*c^5/3 - a*c^7/3 + 2*b^8/3 - b^7*c/3 - b^6*c^2/3 - b^5*c^3/3 + 2*b^4*c^4 - b^3*c^5/3 - b^2*c^6/3 - b*c^7/3 + 2*c^8/3) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (a^8 - a^7 - a^5*b^2 - a^5*c^2 + 2*a^4*b^4 + 2*a^4*c^4 - a^2*b^5 - a^2*c^5 + b^8 - b^7 - b^5*c^2 + 2*b^4*c^4 - b^2*c^5 + c^8 - c^7) = (2*a^8/3 - a^7*b/3 - a^7*c/3 - a^6*b^2/3 - a^6*c^2/3 - a^5*b^3/3 - a^5*b^2*c/3 - a^5*b*c^2/3 - a^5*c^3/3 + 2*a^4*b^4 + 2*a^4*c^4 - a^3*b^5/3 - a^3*c^5/3 - a^2*b^6/3 - a^2*b^5*c/3 - a^2*b*c^5/3 - a^2*c^6/3 - a*b^7/3 - a*b^5*c^2/3 - a*b^2*c^5/3 - a*c^7/3 + 2*b^8/3 - b^7*c/3 - b^6*c^2/3 - b^5*c^3/3 + 2*b^4*c^4 - b^3*c^5/3 - b^2*c^6/3 - b*c^7/3 + 2*c^8/3) := by
    linear_combination (a^7/3 + a^5*b^2/3 + a^5*c^2/3 + a^2*b^5/3 + a^2*c^5/3 + b^7/3 + b^5*c^2/3 + b^2*c^5/3 + c^7/3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3), (a^4 + b^4 + c^4)^2 ≥ (a^2 + b^2 + c^2) * (a^5 + b^5 + c^5)) := @solution
#print axioms solution
