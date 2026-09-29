-- Prove2me | solution 1 for WorkbookSource.base_17037
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:06:39.381222+00:00
-- url     : https://prove2.me/submissions/fb98a881-b1c1-4370-8619-cd25ab2236b8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 ≥ 3 / 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^7*b + 4*a^7*c + 5*a^6*b^2 + 14*a^6*b*c + 5*a^6*c^2 - 2*a^5*b^3 + 10*a^5*b^2*c + 10*a^5*b*c^2 - 2*a^5*c^3 - 6*a^4*b^4 - 12*a^4*b^3*c - 4*a^4*b^2*c^2 - 12*a^4*b*c^3 - 6*a^4*c^4 - 2*a^3*b^5 - 12*a^3*b^4*c - 14*a^3*b^3*c^2 - 14*a^3*b^2*c^3 - 12*a^3*b*c^4 - 2*a^3*c^5 + 5*a^2*b^6 + 10*a^2*b^5*c - 4*a^2*b^4*c^2 - 14*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 10*a^2*b*c^5 + 5*a^2*c^6 + 4*a*b^7 + 14*a*b^6*c + 10*a*b^5*c^2 - 12*a*b^4*c^3 - 12*a*b^3*c^4 + 10*a*b^2*c^5 + 14*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 5*b^6*c^2 - 2*b^5*c^3 - 6*b^4*c^4 - 2*b^3*c^5 + 5*b^2*c^6 + 4*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (288 : ℝ) * a^6 * (b - a)^2 + (288 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (288 : ℝ) * a^6 * (c - b)^2 + (1024 : ℝ) * a^5 * (b - a)^3 + (1536 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (1920 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (704 : ℝ) * a^5 * (c - b)^3 + (1480 : ℝ) * a^4 * (b - a)^4 + (2960 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (4600 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (3120 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (680 : ℝ) * a^4 * (c - b)^4 + (1112 : ℝ) * a^3 * (b - a)^5 + (2780 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (5272 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (5128 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (2180 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (328 : ℝ) * a^3 * (c - b)^5 + (456 : ℝ) * a^2 * (b - a)^6 + (1368 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (3115 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (3950 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (2479 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (732 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (80 : ℝ) * a^2 * (c - b)^6 + (96 : ℝ) * a^1 * (b - a)^7 + (336 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (908 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (1430 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (1184 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (514 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (108 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (8 : ℝ) * a^1 * (c - b)^7 + (8 : ℝ) * (b - a)^8 + (32 : ℝ) * (b - a)^7 * (c - b)^1 + (102 : ℝ) * (b - a)^6 * (c - b)^2 + (194 : ℝ) * (b - a)^5 * (c - b)^3 + (199 : ℝ) * (b - a)^4 * (c - b)^4 + (112 : ℝ) * (b - a)^3 * (c - b)^5 + (33 : ℝ) * (b - a)^2 * (c - b)^6 + (4 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^7*b + 4*a^7*c + 5*a^6*b^2 + 14*a^6*b*c + 5*a^6*c^2 - 2*a^5*b^3 + 10*a^5*b^2*c + 10*a^5*b*c^2 - 2*a^5*c^3 - 6*a^4*b^4 - 12*a^4*b^3*c - 4*a^4*b^2*c^2 - 12*a^4*b*c^3 - 6*a^4*c^4 - 2*a^3*b^5 - 12*a^3*b^4*c - 14*a^3*b^3*c^2 - 14*a^3*b^2*c^3 - 12*a^3*b*c^4 - 2*a^3*c^5 + 5*a^2*b^6 + 10*a^2*b^5*c - 4*a^2*b^4*c^2 - 14*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 10*a^2*b*c^5 + 5*a^2*c^6 + 4*a*b^7 + 14*a*b^6*c + 10*a*b^5*c^2 - 12*a*b^4*c^3 - 12*a*b^3*c^4 + 10*a*b^2*c^5 + 14*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 5*b^6*c^2 - 2*b^5*c^3 - 6*b^4*c^4 - 2*b^3*c^5 + 5*b^2*c^6 + 4*b*c^7) := by
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
  have hn : 0 ≤ (4*a^7*b + 4*a^7*c + 5*a^6*b^2 + 14*a^6*b*c + 5*a^6*c^2 - 2*a^5*b^3 + 10*a^5*b^2*c + 10*a^5*b*c^2 - 2*a^5*c^3 - 6*a^4*b^4 - 12*a^4*b^3*c - 4*a^4*b^2*c^2 - 12*a^4*b*c^3 - 6*a^4*c^4 - 2*a^3*b^5 - 12*a^3*b^4*c - 14*a^3*b^3*c^2 - 14*a^3*b^2*c^3 - 12*a^3*b*c^4 - 2*a^3*c^5 + 5*a^2*b^6 + 10*a^2*b^5*c - 4*a^2*b^4*c^2 - 14*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 10*a^2*b*c^5 + 5*a^2*c^6 + 4*a*b^7 + 14*a*b^6*c + 10*a*b^5*c^2 - 12*a*b^4*c^3 - 12*a*b^3*c^4 + 10*a*b^2*c^5 + 14*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 5*b^6*c^2 - 2*b^5*c^3 - 6*b^4*c^4 - 2*b^3*c^5 + 5*b^2*c^6 + 4*b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 ≥ 3 / 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c)) := @solution
#print axioms solution
