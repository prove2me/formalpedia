-- Prove2me | solution 1 for WorkbookSource.base_27509
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:05.535088+00:00
-- url     : https://prove2.me/submissions/70f69aa2-a190-4c7f-9ee8-bc33f8fa6480

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 1 / b + 1 / c) ≥ (4 * a / (2 * a ^ 2 + b ^ 2 + c ^ 2) + 4 * b / (2 * b ^ 2 + c ^ 2 + a ^ 2) + 4 * c / (2 * c ^ 2 + a ^ 2 + b ^ 2))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^7*b + 2*a^7*c - 2*a^6*b*c + 7*a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + 7*a^5*c^3 - 5*a^4*b^3*c - 5*a^4*b*c^3 + 7*a^3*b^5 - 5*a^3*b^4*c - 4*a^3*b^3*c^2 - 4*a^3*b^2*c^3 - 5*a^3*b*c^4 + 7*a^3*c^5 - a^2*b^5*c - 4*a^2*b^3*c^3 - a^2*b*c^5 + 2*a*b^7 - 2*a*b^6*c - a*b^5*c^2 - 5*a*b^4*c^3 - 5*a*b^3*c^4 - a*b^2*c^5 - 2*a*b*c^6 + 2*a*c^7 + 2*b^7*c + 7*b^5*c^3 + 7*b^3*c^5 + 2*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^6 * (b - a)^2 + (96 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^6 * (c - b)^2 + (400 : ℝ) * a^5 * (b - a)^3 + (600 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (552 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (176 : ℝ) * a^5 * (c - b)^3 + (720 : ℝ) * a^4 * (b - a)^4 + (1440 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1480 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (760 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (160 : ℝ) * a^4 * (c - b)^4 + (716 : ℝ) * a^3 * (b - a)^5 + (1790 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (2156 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1444 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (530 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (84 : ℝ) * a^3 * (c - b)^5 + (414 : ℝ) * a^2 * (b - a)^6 + (1242 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1753 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1436 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (715 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (204 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (26 : ℝ) * a^2 * (c - b)^6 + (132 : ℝ) * a^1 * (b - a)^7 + (462 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (754 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (730 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (450 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (176 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (40 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * a^1 * (c - b)^7 + (18 : ℝ) * (b - a)^8 + (72 : ℝ) * (b - a)^7 * (c - b)^1 + (133 : ℝ) * (b - a)^6 * (c - b)^2 + (147 : ℝ) * (b - a)^5 * (c - b)^3 + (105 : ℝ) * (b - a)^4 * (c - b)^4 + (49 : ℝ) * (b - a)^3 * (c - b)^5 + (14 : ℝ) * (b - a)^2 * (c - b)^6 + (2 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^7*b + 2*a^7*c - 2*a^6*b*c + 7*a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + 7*a^5*c^3 - 5*a^4*b^3*c - 5*a^4*b*c^3 + 7*a^3*b^5 - 5*a^3*b^4*c - 4*a^3*b^3*c^2 - 4*a^3*b^2*c^3 - 5*a^3*b*c^4 + 7*a^3*c^5 - a^2*b^5*c - 4*a^2*b^3*c^3 - a^2*b*c^5 + 2*a*b^7 - 2*a*b^6*c - a*b^5*c^2 - 5*a*b^4*c^3 - 5*a*b^3*c^4 - a*b^2*c^5 - 2*a*b*c^6 + 2*a*c^7 + 2*b^7*c + 7*b^5*c^3 + 7*b^3*c^5 + 2*b*c^7) := by
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
  have hn : 0 ≤ (2*a^7*b + 2*a^7*c - 2*a^6*b*c + 7*a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + 7*a^5*c^3 - 5*a^4*b^3*c - 5*a^4*b*c^3 + 7*a^3*b^5 - 5*a^3*b^4*c - 4*a^3*b^3*c^2 - 4*a^3*b^2*c^3 - 5*a^3*b*c^4 + 7*a^3*c^5 - a^2*b^5*c - 4*a^2*b^3*c^3 - a^2*b*c^5 + 2*a*b^7 - 2*a*b^6*c - a*b^5*c^2 - 5*a*b^4*c^3 - 5*a*b^3*c^4 - a*b^2*c^5 - 2*a*b*c^6 + 2*a*c^7 + 2*b^7*c + 7*b^5*c^3 + 7*b^3*c^5 + 2*b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / a + 1 / b + 1 / c) ≥ (4 * a / (2 * a ^ 2 + b ^ 2 + c ^ 2) + 4 * b / (2 * b ^ 2 + c ^ 2 + a ^ 2) + 4 * c / (2 * c ^ 2 + a ^ 2 + b ^ 2))) := @solution
#print axioms solution
