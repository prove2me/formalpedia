-- Prove2me | solution 1 for WorkbookSource.plus_60608
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:48.5571+00:00
-- url     : https://prove2.me/submissions/5db3647e-3958-4b00-8400-fa280cd34eda

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c - a) ^ 2 / (17 * a ^ 2 + 7 * (b + c) ^ 2) + (c + a - b) ^ 2 / (17 * b ^ 2 + 7 * (c + a) ^ 2) + (a + b - c) ^ 2 / (17 * c ^ 2 + 7 * (a + b) ^ 2) ≥ (a ^ 2 + b ^ 2 + c ^ 2) / (5 * (a + b + c) ^ 2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (602*a^8 + 2394*a^7*b + 2394*a^7*c + 1228*a^6*b^2 + 6482*a^6*b*c + 1228*a^6*c^2 + 1062*a^5*b^3 + 3710*a^5*b^2*c + 3710*a^5*b*c^2 + 1062*a^5*c^3 + 3252*a^4*b^4 - 4522*a^4*b^3*c - 10900*a^4*b^2*c^2 - 4522*a^4*b*c^3 + 3252*a^4*c^4 + 1062*a^3*b^5 - 4522*a^3*b^4*c - 7180*a^3*b^3*c^2 - 7180*a^3*b^2*c^3 - 4522*a^3*b*c^4 + 1062*a^3*c^5 + 1228*a^2*b^6 + 3710*a^2*b^5*c - 10900*a^2*b^4*c^2 - 7180*a^2*b^3*c^3 - 10900*a^2*b^2*c^4 + 3710*a^2*b*c^5 + 1228*a^2*c^6 + 2394*a*b^7 + 6482*a*b^6*c + 3710*a*b^5*c^2 - 4522*a*b^4*c^3 - 4522*a*b^3*c^4 + 3710*a*b^2*c^5 + 6482*a*b*c^6 + 2394*a*c^7 + 602*b^8 + 2394*b^7*c + 1228*b^6*c^2 + 1062*b^5*c^3 + 3252*b^4*c^4 + 1062*b^3*c^5 + 1228*b^2*c^6 + 2394*b*c^7 + 602*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (183330 : ℝ) * a^6 * (b - a)^2 + (183330 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (183330 : ℝ) * a^6 * (c - b)^2 + (699528 : ℝ) * a^5 * (b - a)^3 + (1049292 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (1150668 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (400452 : ℝ) * a^5 * (c - b)^3 + (1125760 : ℝ) * a^4 * (b - a)^4 + (2251520 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (2883030 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (1757270 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (378070 : ℝ) * a^4 * (c - b)^4 + (976928 : ℝ) * a^3 * (b - a)^5 + (2442320 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (3663568 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (3053032 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (1249720 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (197432 : ℝ) * a^3 * (c - b)^5 + (480864 : ℝ) * a^2 * (b - a)^6 + (1442592 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (2497200 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (2590080 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (1528686 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (474078 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (59310 : ℝ) * a^2 * (c - b)^6 + (126720 : ℝ) * a^1 * (b - a)^7 + (443520 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (868192 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (1061680 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (806696 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (370124 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (92924 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (9604 : ℝ) * a^1 * (c - b)^7 + (13824 : ℝ) * (b - a)^8 + (55296 : ℝ) * (b - a)^7 * (c - b)^1 + (120096 : ℝ) * (b - a)^6 * (c - b)^2 + (166752 : ℝ) * (b - a)^5 * (c - b)^3 + (152912 : ℝ) * (b - a)^4 * (c - b)^4 + (92416 : ℝ) * (b - a)^3 * (c - b)^5 + (34842 : ℝ) * (b - a)^2 * (c - b)^6 + (7210 : ℝ) * (b - a)^1 * (c - b)^7 + (602 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (602*a^8 + 2394*a^7*b + 2394*a^7*c + 1228*a^6*b^2 + 6482*a^6*b*c + 1228*a^6*c^2 + 1062*a^5*b^3 + 3710*a^5*b^2*c + 3710*a^5*b*c^2 + 1062*a^5*c^3 + 3252*a^4*b^4 - 4522*a^4*b^3*c - 10900*a^4*b^2*c^2 - 4522*a^4*b*c^3 + 3252*a^4*c^4 + 1062*a^3*b^5 - 4522*a^3*b^4*c - 7180*a^3*b^3*c^2 - 7180*a^3*b^2*c^3 - 4522*a^3*b*c^4 + 1062*a^3*c^5 + 1228*a^2*b^6 + 3710*a^2*b^5*c - 10900*a^2*b^4*c^2 - 7180*a^2*b^3*c^3 - 10900*a^2*b^2*c^4 + 3710*a^2*b*c^5 + 1228*a^2*c^6 + 2394*a*b^7 + 6482*a*b^6*c + 3710*a*b^5*c^2 - 4522*a*b^4*c^3 - 4522*a*b^3*c^4 + 3710*a*b^2*c^5 + 6482*a*b*c^6 + 2394*a*c^7 + 602*b^8 + 2394*b^7*c + 1228*b^6*c^2 + 1062*b^5*c^3 + 3252*b^4*c^4 + 1062*b^3*c^5 + 1228*b^2*c^6 + 2394*b*c^7 + 602*c^8) := by
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
  have hn : 0 ≤ (602*a^8 + 2394*a^7*b + 2394*a^7*c + 1228*a^6*b^2 + 6482*a^6*b*c + 1228*a^6*c^2 + 1062*a^5*b^3 + 3710*a^5*b^2*c + 3710*a^5*b*c^2 + 1062*a^5*c^3 + 3252*a^4*b^4 - 4522*a^4*b^3*c - 10900*a^4*b^2*c^2 - 4522*a^4*b*c^3 + 3252*a^4*c^4 + 1062*a^3*b^5 - 4522*a^3*b^4*c - 7180*a^3*b^3*c^2 - 7180*a^3*b^2*c^3 - 4522*a^3*b*c^4 + 1062*a^3*c^5 + 1228*a^2*b^6 + 3710*a^2*b^5*c - 10900*a^2*b^4*c^2 - 7180*a^2*b^3*c^3 - 10900*a^2*b^2*c^4 + 3710*a^2*b*c^5 + 1228*a^2*c^6 + 2394*a*b^7 + 6482*a*b^6*c + 3710*a*b^5*c^2 - 4522*a*b^4*c^3 - 4522*a*b^3*c^4 + 3710*a*b^2*c^5 + 6482*a*b*c^6 + 2394*a*c^7 + 602*b^8 + 2394*b^7*c + 1228*b^6*c^2 + 1062*b^5*c^3 + 3252*b^4*c^4 + 1062*b^3*c^5 + 1228*b^2*c^6 + 2394*b*c^7 + 602*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (b + c - a) ^ 2 / (17 * a ^ 2 + 7 * (b + c) ^ 2) + (c + a - b) ^ 2 / (17 * b ^ 2 + 7 * (c + a) ^ 2) + (a + b - c) ^ 2 / (17 * c ^ 2 + 7 * (a + b) ^ 2) ≥ (a ^ 2 + b ^ 2 + c ^ 2) / (5 * (a + b + c) ^ 2)) := @solution
#print axioms solution
