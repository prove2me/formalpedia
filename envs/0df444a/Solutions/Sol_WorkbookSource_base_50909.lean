-- Prove2me | solution 1 for WorkbookSource.base_50909
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:35:35.552417+00:00
-- url     : https://prove2.me/submissions/3766351a-808f-447a-af2f-20487b4c4238

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (3 * (a * b + a * c + b * c)) ≥ a / (2 * a + 7 * b) + b / (2 * b + 7 * c) + c / (2 * c + 7 * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (28*a^4*b + 98*a^4*c + 14*a^3*b^2 + 120*a^3*b*c - 119*a^3*c^2 - 119*a^2*b^3 - 141*a^2*b^2*c - 141*a^2*b*c^2 + 14*a^2*c^3 + 98*a*b^4 + 120*a*b^3*c - 141*a*b^2*c^2 + 120*a*b*c^3 + 28*a*c^4 + 28*b^4*c + 14*b^3*c^2 - 119*b^2*c^3 + 98*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (414 : ℝ) * a^3 * (b - a)^2 + (414 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (414 : ℝ) * a^3 * (c - b)^2 + (723 : ℝ) * a^2 * (b - a)^3 + (1095 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (1410 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (519 : ℝ) * a^2 * (c - b)^3 + (330 : ℝ) * a^1 * (b - a)^4 + (674 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (1122 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (778 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (126 : ℝ) * a^1 * (c - b)^4 + (21 : ℝ) * (b - a)^5 + (91 : ℝ) * (b - a)^4 * (c - b)^1 + (245 : ℝ) * (b - a)^3 * (c - b)^2 + (273 : ℝ) * (b - a)^2 * (c - b)^3 + (98 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (28*a^4*b + 98*a^4*c + 14*a^3*b^2 + 120*a^3*b*c - 119*a^3*c^2 - 119*a^2*b^3 - 141*a^2*b^2*c - 141*a^2*b*c^2 + 14*a^2*c^3 + 98*a*b^4 + 120*a*b^3*c - 141*a*b^2*c^2 + 120*a*b*c^3 + 28*a*c^4 + 28*b^4*c + 14*b^3*c^2 - 119*b^2*c^3 + 98*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (414 : ℝ) * a^3 * (c - a)^2 + (414 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (414 : ℝ) * a^3 * (b - c)^2 + (723 : ℝ) * a^2 * (c - a)^3 + (1074 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (1389 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (519 : ℝ) * a^2 * (b - c)^3 + (330 : ℝ) * a^1 * (c - a)^4 + (646 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (1080 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (764 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (126 : ℝ) * a^1 * (b - c)^4 + (21 : ℝ) * (c - a)^5 + (14 : ℝ) * (c - a)^4 * (b - c)^1 + (91 : ℝ) * (c - a)^3 * (b - c)^2 + (126 : ℝ) * (c - a)^2 * (b - c)^3 + (28 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (28*a^4*b + 98*a^4*c + 14*a^3*b^2 + 120*a^3*b*c - 119*a^3*c^2 - 119*a^2*b^3 - 141*a^2*b^2*c - 141*a^2*b*c^2 + 14*a^2*c^3 + 98*a*b^4 + 120*a*b^3*c - 141*a*b^2*c^2 + 120*a*b*c^3 + 28*a*c^4 + 28*b^4*c + 14*b^3*c^2 - 119*b^2*c^3 + 98*b*c^4) := by
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
  have hn : 0 ≤ (28*a^4*b + 98*a^4*c + 14*a^3*b^2 + 120*a^3*b*c - 119*a^3*c^2 - 119*a^2*b^3 - 141*a^2*b^2*c - 141*a^2*b*c^2 + 14*a^2*c^3 + 98*a*b^4 + 120*a*b^3*c - 141*a*b^2*c^2 + 120*a*b*c^3 + 28*a*c^4 + 28*b^4*c + 14*b^3*c^2 - 119*b^2*c^3 + 98*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) / (3 * (a * b + a * c + b * c)) ≥ a / (2 * a + 7 * b) + b / (2 * b + 7 * c) + c / (2 * c + 7 * a)) := @solution
#print axioms solution
