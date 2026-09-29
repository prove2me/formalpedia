-- Prove2me | solution 1 for WorkbookSource.plus_49894
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:28:57.037986+00:00
-- url     : https://prove2.me/submissions/bf96e6bf-4963-4865-b1c2-e14a33893bef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 3 / (3 * a ^ 2 + 3 * a * b + b ^ 2) + (b + c) ^ 3 / (3 * b ^ 2 + 3 * b * c + c ^ 2) + (c + a) ^ 3 / (3 * c ^ 2 + 3 * c * a + a ^ 2) ≥ 8 / 7 * (a + b + c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (12*a^5*b^2 + 12*a^5*b*c + 4*a^5*c^2 + 3*a^4*b^3 + 9*a^4*b^2*c + 21*a^4*b*c^2 + 9*a^4*c^3 + 9*a^3*b^4 - 12*a^3*b^3*c - 58*a^3*b^2*c^2 - 12*a^3*b*c^3 + 3*a^3*c^4 + 4*a^2*b^5 + 21*a^2*b^4*c - 58*a^2*b^3*c^2 - 58*a^2*b^2*c^3 + 9*a^2*b*c^4 + 12*a^2*c^5 + 12*a*b^5*c + 9*a*b^4*c^2 - 12*a*b^3*c^3 + 21*a*b^2*c^4 + 12*a*b*c^5 + 12*b^5*c^2 + 3*b^4*c^3 + 9*b^3*c^4 + 4*b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (252 : ℝ) * a^5 * (b - a)^2 + (252 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (252 : ℝ) * a^5 * (c - b)^2 + (882 : ℝ) * a^4 * (b - a)^3 + (1299 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (1173 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (378 : ℝ) * a^4 * (c - b)^3 + (1190 : ℝ) * a^3 * (b - a)^4 + (2316 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (2214 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (1088 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (182 : ℝ) * a^3 * (c - b)^4 + (770 : ℝ) * a^2 * (b - a)^5 + (1852 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (1968 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (1148 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (318 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (28 : ℝ) * a^2 * (c - b)^5 + (238 : ℝ) * a^1 * (b - a)^6 + (672 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (794 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (508 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (168 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (20 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (28 : ℝ) * (b - a)^7 + (89 : ℝ) * (b - a)^6 * (c - b)^1 + (115 : ℝ) * (b - a)^5 * (c - b)^2 + (79 : ℝ) * (b - a)^4 * (c - b)^3 + (29 : ℝ) * (b - a)^3 * (c - b)^4 + (4 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (12*a^5*b^2 + 12*a^5*b*c + 4*a^5*c^2 + 3*a^4*b^3 + 9*a^4*b^2*c + 21*a^4*b*c^2 + 9*a^4*c^3 + 9*a^3*b^4 - 12*a^3*b^3*c - 58*a^3*b^2*c^2 - 12*a^3*b*c^3 + 3*a^3*c^4 + 4*a^2*b^5 + 21*a^2*b^4*c - 58*a^2*b^3*c^2 - 58*a^2*b^2*c^3 + 9*a^2*b*c^4 + 12*a^2*c^5 + 12*a*b^5*c + 9*a*b^4*c^2 - 12*a*b^3*c^3 + 21*a*b^2*c^4 + 12*a*b*c^5 + 12*b^5*c^2 + 3*b^4*c^3 + 9*b^3*c^4 + 4*b^2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (252 : ℝ) * a^5 * (c - a)^2 + (252 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (252 : ℝ) * a^5 * (b - c)^2 + (882 : ℝ) * a^4 * (c - a)^3 + (1347 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (1221 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (378 : ℝ) * a^4 * (b - c)^3 + (1190 : ℝ) * a^3 * (c - a)^4 + (2444 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (2406 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (1152 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (182 : ℝ) * a^3 * (b - c)^4 + (770 : ℝ) * a^2 * (c - a)^5 + (1998 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (2260 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (1344 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (368 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (28 : ℝ) * a^2 * (b - c)^5 + (238 : ℝ) * a^1 * (c - a)^6 + (756 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (1004 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (708 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (258 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (36 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (28 : ℝ) * (c - a)^7 + (107 : ℝ) * (c - a)^6 * (b - c)^1 + (169 : ℝ) * (c - a)^5 * (b - c)^2 + (141 : ℝ) * (c - a)^4 * (b - c)^3 + (63 : ℝ) * (c - a)^3 * (b - c)^4 + (12 : ℝ) * (c - a)^2 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (12*a^5*b^2 + 12*a^5*b*c + 4*a^5*c^2 + 3*a^4*b^3 + 9*a^4*b^2*c + 21*a^4*b*c^2 + 9*a^4*c^3 + 9*a^3*b^4 - 12*a^3*b^3*c - 58*a^3*b^2*c^2 - 12*a^3*b*c^3 + 3*a^3*c^4 + 4*a^2*b^5 + 21*a^2*b^4*c - 58*a^2*b^3*c^2 - 58*a^2*b^2*c^3 + 9*a^2*b*c^4 + 12*a^2*c^5 + 12*a*b^5*c + 9*a*b^4*c^2 - 12*a*b^3*c^3 + 21*a*b^2*c^4 + 12*a*b*c^5 + 12*b^5*c^2 + 3*b^4*c^3 + 9*b^3*c^4 + 4*b^2*c^5) := by
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
  have hn : 0 ≤ (12*a^5*b^2 + 12*a^5*b*c + 4*a^5*c^2 + 3*a^4*b^3 + 9*a^4*b^2*c + 21*a^4*b*c^2 + 9*a^4*c^3 + 9*a^3*b^4 - 12*a^3*b^3*c - 58*a^3*b^2*c^2 - 12*a^3*b*c^3 + 3*a^3*c^4 + 4*a^2*b^5 + 21*a^2*b^4*c - 58*a^2*b^3*c^2 - 58*a^2*b^2*c^3 + 9*a^2*b*c^4 + 12*a^2*c^5 + 12*a*b^5*c + 9*a*b^4*c^2 - 12*a*b^3*c^3 + 21*a*b^2*c^4 + 12*a*b*c^5 + 12*b^5*c^2 + 3*b^4*c^3 + 9*b^3*c^4 + 4*b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) ^ 3 / (3 * a ^ 2 + 3 * a * b + b ^ 2) + (b + c) ^ 3 / (3 * b ^ 2 + 3 * b * c + c ^ 2) + (c + a) ^ 3 / (3 * c ^ 2 + 3 * c * a + a ^ 2) ≥ 8 / 7 * (a + b + c)) := @solution
#print axioms solution
