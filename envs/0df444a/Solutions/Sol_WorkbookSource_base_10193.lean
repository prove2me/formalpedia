-- Prove2me | solution 1 for WorkbookSource.base_10193
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:32:31.677436+00:00
-- url     : https://prove2.me/submissions/d42498ae-3705-40a0-b5f6-e305d2ec6186

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b^2 / (a + b) / (2 * a + b) + b^2 * c^2 / (b + c) / (2 * b + c) + c^2 * a^2 / (c + a) / (2 * c + a)) ≤ (a + b + c)^2 / 18  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6*b^2 + 6*a^6*b*c + 2*a^6*c^2 + 14*a^5*b^3 + 41*a^5*b^2*c + 37*a^5*b*c^2 + 10*a^5*c^3 - 18*a^4*b^4 + 35*a^4*b^3*c + 12*a^4*b^2*c^2 - 23*a^4*b*c^3 - 18*a^4*c^4 + 10*a^3*b^5 - 23*a^3*b^4*c - 120*a^3*b^3*c^2 - 120*a^3*b^2*c^3 + 35*a^3*b*c^4 + 14*a^3*c^5 + 2*a^2*b^6 + 37*a^2*b^5*c + 12*a^2*b^4*c^2 - 120*a^2*b^3*c^3 + 12*a^2*b^2*c^4 + 41*a^2*b*c^5 + 4*a^2*c^6 + 6*a*b^6*c + 41*a*b^5*c^2 + 35*a*b^4*c^3 - 23*a*b^3*c^4 + 37*a*b^2*c^5 + 6*a*b*c^6 + 4*b^6*c^2 + 14*b^5*c^3 - 18*b^4*c^4 + 10*b^3*c^5 + 2*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (504 : ℝ) * a^6 * (b - a)^2 + (504 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (504 : ℝ) * a^6 * (c - b)^2 + (2016 : ℝ) * a^5 * (b - a)^3 + (2871 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (2871 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (1008 : ℝ) * a^5 * (c - b)^3 + (3198 : ℝ) * a^4 * (b - a)^4 + (5886 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (6309 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (3621 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (678 : ℝ) * a^4 * (c - b)^4 + (2538 : ℝ) * a^3 * (b - a)^5 + (5707 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (6686 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (4832 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (1663 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (174 : ℝ) * a^3 * (c - b)^5 + (1038 : ℝ) * a^2 * (b - a)^6 + (2750 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (3554 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (2970 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (1405 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (277 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (12 : ℝ) * a^2 * (c - b)^6 + (198 : ℝ) * a^1 * (b - a)^7 + (602 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (876 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (843 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (500 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (139 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (12 : ℝ) * (b - a)^8 + (40 : ℝ) * (b - a)^7 * (c - b)^1 + (68 : ℝ) * (b - a)^6 * (c - b)^2 + (82 : ℝ) * (b - a)^5 * (c - b)^3 + (62 : ℝ) * (b - a)^4 * (c - b)^4 + (22 : ℝ) * (b - a)^3 * (c - b)^5 + (2 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^6*b^2 + 6*a^6*b*c + 2*a^6*c^2 + 14*a^5*b^3 + 41*a^5*b^2*c + 37*a^5*b*c^2 + 10*a^5*c^3 - 18*a^4*b^4 + 35*a^4*b^3*c + 12*a^4*b^2*c^2 - 23*a^4*b*c^3 - 18*a^4*c^4 + 10*a^3*b^5 - 23*a^3*b^4*c - 120*a^3*b^3*c^2 - 120*a^3*b^2*c^3 + 35*a^3*b*c^4 + 14*a^3*c^5 + 2*a^2*b^6 + 37*a^2*b^5*c + 12*a^2*b^4*c^2 - 120*a^2*b^3*c^3 + 12*a^2*b^2*c^4 + 41*a^2*b*c^5 + 4*a^2*c^6 + 6*a*b^6*c + 41*a*b^5*c^2 + 35*a*b^4*c^3 - 23*a*b^3*c^4 + 37*a*b^2*c^5 + 6*a*b*c^6 + 4*b^6*c^2 + 14*b^5*c^3 - 18*b^4*c^4 + 10*b^3*c^5 + 2*b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (504 : ℝ) * a^6 * (c - a)^2 + (504 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (504 : ℝ) * a^6 * (b - c)^2 + (2016 : ℝ) * a^5 * (c - a)^3 + (3177 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (3177 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (1008 : ℝ) * a^5 * (b - c)^3 + (3198 : ℝ) * a^4 * (c - a)^4 + (6906 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (7839 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (4131 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (678 : ℝ) * a^4 * (b - c)^4 + (2538 : ℝ) * a^3 * (c - a)^5 + (6983 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (9238 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (6364 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (1919 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (174 : ℝ) * a^3 * (b - c)^5 + (1038 : ℝ) * a^2 * (c - a)^6 + (3478 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (5374 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (4506 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (1889 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (317 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (12 : ℝ) * a^2 * (b - c)^6 + (198 : ℝ) * a^1 * (c - a)^7 + (784 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (1422 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (1437 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (778 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (191 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (14 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (12 : ℝ) * (c - a)^8 + (56 : ℝ) * (c - a)^7 * (b - c)^1 + (124 : ℝ) * (c - a)^6 * (b - c)^2 + (158 : ℝ) * (c - a)^5 * (b - c)^3 + (112 : ℝ) * (c - a)^4 * (b - c)^4 + (38 : ℝ) * (c - a)^3 * (b - c)^5 + (4 : ℝ) * (c - a)^2 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6*b^2 + 6*a^6*b*c + 2*a^6*c^2 + 14*a^5*b^3 + 41*a^5*b^2*c + 37*a^5*b*c^2 + 10*a^5*c^3 - 18*a^4*b^4 + 35*a^4*b^3*c + 12*a^4*b^2*c^2 - 23*a^4*b*c^3 - 18*a^4*c^4 + 10*a^3*b^5 - 23*a^3*b^4*c - 120*a^3*b^3*c^2 - 120*a^3*b^2*c^3 + 35*a^3*b*c^4 + 14*a^3*c^5 + 2*a^2*b^6 + 37*a^2*b^5*c + 12*a^2*b^4*c^2 - 120*a^2*b^3*c^3 + 12*a^2*b^2*c^4 + 41*a^2*b*c^5 + 4*a^2*c^6 + 6*a*b^6*c + 41*a*b^5*c^2 + 35*a*b^4*c^3 - 23*a*b^3*c^4 + 37*a*b^2*c^5 + 6*a*b*c^6 + 4*b^6*c^2 + 14*b^5*c^3 - 18*b^4*c^4 + 10*b^3*c^5 + 2*b^2*c^6) := by
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
  have hn : 0 ≤ (4*a^6*b^2 + 6*a^6*b*c + 2*a^6*c^2 + 14*a^5*b^3 + 41*a^5*b^2*c + 37*a^5*b*c^2 + 10*a^5*c^3 - 18*a^4*b^4 + 35*a^4*b^3*c + 12*a^4*b^2*c^2 - 23*a^4*b*c^3 - 18*a^4*c^4 + 10*a^3*b^5 - 23*a^3*b^4*c - 120*a^3*b^3*c^2 - 120*a^3*b^2*c^3 + 35*a^3*b*c^4 + 14*a^3*c^5 + 2*a^2*b^6 + 37*a^2*b^5*c + 12*a^2*b^4*c^2 - 120*a^2*b^3*c^3 + 12*a^2*b^2*c^4 + 41*a^2*b*c^5 + 4*a^2*c^6 + 6*a*b^6*c + 41*a*b^5*c^2 + 35*a*b^4*c^3 - 23*a*b^3*c^4 + 37*a*b^2*c^5 + 6*a*b*c^6 + 4*b^6*c^2 + 14*b^5*c^3 - 18*b^4*c^4 + 10*b^3*c^5 + 2*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 * b^2 / (a + b) / (2 * a + b) + b^2 * c^2 / (b + c) / (2 * b + c) + c^2 * a^2 / (c + a) / (2 * c + a)) ≤ (a + b + c)^2 / 18) := @solution
#print axioms solution
