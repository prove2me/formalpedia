-- Prove2me | solution 1 for WorkbookSource.base_49763
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:42.913227+00:00
-- url     : https://prove2.me/submissions/71e9dab9-510e-47ae-8c96-25e7f2e51060

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (b + c) * (a / (2 * a + b + c)) + (b + c) / (c + a) * (b / (2 * b + c + a)) + (c + a) / (a + b) * (c / (2 * c + a + b)) ≥ 3 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6 + 14*a^5*b + 10*a^5*c + 9*a^4*b^2 + 18*a^4*b*c + a^4*c^2 - 6*a^3*b^3 - 14*a^3*b^2*c - 22*a^3*b*c^2 - 6*a^3*c^3 + a^2*b^4 - 22*a^2*b^3*c - 42*a^2*b^2*c^2 - 14*a^2*b*c^3 + 9*a^2*c^4 + 10*a*b^5 + 18*a*b^4*c - 14*a*b^3*c^2 - 22*a*b^2*c^3 + 18*a*b*c^4 + 14*a*c^5 + 4*b^6 + 14*b^5*c + 9*b^4*c^2 - 6*b^3*c^3 + b^2*c^4 + 10*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (256 : ℝ) * a^4 * (b - a)^2 + (256 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (256 : ℝ) * a^4 * (c - b)^2 + (640 : ℝ) * a^3 * (b - a)^3 + (904 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1032 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (384 : ℝ) * a^3 * (c - b)^3 + (592 : ℝ) * a^2 * (b - a)^4 + (1072 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1416 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (936 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (208 : ℝ) * a^2 * (c - b)^4 + (240 : ℝ) * a^1 * (b - a)^5 + (526 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (796 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (724 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (310 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (48 : ℝ) * a^1 * (c - b)^5 + (36 : ℝ) * (b - a)^6 + (92 : ℝ) * (b - a)^5 * (c - b)^1 + (157 : ℝ) * (b - a)^4 * (c - b)^2 + (178 : ℝ) * (b - a)^3 * (c - b)^3 + (111 : ℝ) * (b - a)^2 * (c - b)^4 + (34 : ℝ) * (b - a)^1 * (c - b)^5 + (4 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^6 + 14*a^5*b + 10*a^5*c + 9*a^4*b^2 + 18*a^4*b*c + a^4*c^2 - 6*a^3*b^3 - 14*a^3*b^2*c - 22*a^3*b*c^2 - 6*a^3*c^3 + a^2*b^4 - 22*a^2*b^3*c - 42*a^2*b^2*c^2 - 14*a^2*b*c^3 + 9*a^2*c^4 + 10*a*b^5 + 18*a*b^4*c - 14*a*b^3*c^2 - 22*a*b^2*c^3 + 18*a*b*c^4 + 14*a*c^5 + 4*b^6 + 14*b^5*c + 9*b^4*c^2 - 6*b^3*c^3 + b^2*c^4 + 10*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (256 : ℝ) * a^4 * (c - a)^2 + (256 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (256 : ℝ) * a^4 * (b - c)^2 + (640 : ℝ) * a^3 * (c - a)^3 + (1016 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (1144 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (384 : ℝ) * a^3 * (b - c)^3 + (592 : ℝ) * a^2 * (c - a)^4 + (1296 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (1752 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (1048 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (208 : ℝ) * a^2 * (b - c)^4 + (240 : ℝ) * a^1 * (c - a)^5 + (674 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (1092 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (908 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (346 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (48 : ℝ) * a^1 * (b - c)^5 + (36 : ℝ) * (c - a)^6 + (124 : ℝ) * (c - a)^5 * (b - c)^1 + (237 : ℝ) * (c - a)^4 * (b - c)^2 + (250 : ℝ) * (c - a)^3 * (b - c)^3 + (139 : ℝ) * (c - a)^2 * (b - c)^4 + (38 : ℝ) * (c - a)^1 * (b - c)^5 + (4 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6 + 14*a^5*b + 10*a^5*c + 9*a^4*b^2 + 18*a^4*b*c + a^4*c^2 - 6*a^3*b^3 - 14*a^3*b^2*c - 22*a^3*b*c^2 - 6*a^3*c^3 + a^2*b^4 - 22*a^2*b^3*c - 42*a^2*b^2*c^2 - 14*a^2*b*c^3 + 9*a^2*c^4 + 10*a*b^5 + 18*a*b^4*c - 14*a*b^3*c^2 - 22*a*b^2*c^3 + 18*a*b*c^4 + 14*a*c^5 + 4*b^6 + 14*b^5*c + 9*b^4*c^2 - 6*b^3*c^3 + b^2*c^4 + 10*b*c^5 + 4*c^6) := by
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
  have hn : 0 ≤ (4*a^6 + 14*a^5*b + 10*a^5*c + 9*a^4*b^2 + 18*a^4*b*c + a^4*c^2 - 6*a^3*b^3 - 14*a^3*b^2*c - 22*a^3*b*c^2 - 6*a^3*c^3 + a^2*b^4 - 22*a^2*b^3*c - 42*a^2*b^2*c^2 - 14*a^2*b*c^3 + 9*a^2*c^4 + 10*a*b^5 + 18*a*b^4*c - 14*a*b^3*c^2 - 22*a*b^2*c^3 + 18*a*b*c^4 + 14*a*c^5 + 4*b^6 + 14*b^5*c + 9*b^4*c^2 - 6*b^3*c^3 + b^2*c^4 + 10*b*c^5 + 4*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (b + c) * (a / (2 * a + b + c)) + (b + c) / (c + a) * (b / (2 * b + c + a)) + (c + a) / (a + b) * (c / (2 * c + a + b)) ≥ 3 / 4) := @solution
#print axioms solution
