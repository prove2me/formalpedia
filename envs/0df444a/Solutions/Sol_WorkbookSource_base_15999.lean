-- Prove2me | solution 1 for WorkbookSource.base_15999
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:05.462329+00:00
-- url     : https://prove2.me/submissions/3836a01c-b95d-4e5b-9d27-21176d058f8a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 + 3 ≥ 5 * (a + b + c) ^ 2 / (4 * (a * b + b * c + a * c))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^7*b + 4*a^7*c + 3*a^6*b^2 + 10*a^6*b*c + 3*a^6*c^2 - 4*a^5*b^3 + 4*a^5*b^2*c + 4*a^5*b*c^2 - 4*a^5*c^3 - 6*a^4*b^4 - 10*a^4*b^3*c - 10*a^4*b*c^3 - 6*a^4*c^4 - 4*a^3*b^5 - 10*a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 10*a^3*b*c^4 - 4*a^3*c^5 + 3*a^2*b^6 + 4*a^2*b^5*c + 2*a^2*b^3*c^3 + 4*a^2*b*c^5 + 3*a^2*c^6 + 4*a*b^7 + 10*a*b^6*c + 4*a*b^5*c^2 - 10*a*b^4*c^3 - 10*a*b^3*c^4 + 4*a*b^2*c^5 + 10*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 3*b^6*c^2 - 4*b^5*c^3 - 6*b^4*c^4 - 4*b^3*c^5 + 3*b^2*c^6 + 4*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (160 : ℝ) * a^6 * (b - a)^2 + (160 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (160 : ℝ) * a^6 * (c - b)^2 + (512 : ℝ) * a^5 * (b - a)^3 + (768 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (1152 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (448 : ℝ) * a^5 * (c - b)^3 + (648 : ℝ) * a^4 * (b - a)^4 + (1296 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (2744 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (2096 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (488 : ℝ) * a^4 * (c - b)^4 + (408 : ℝ) * a^3 * (b - a)^5 + (1020 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (3032 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (3528 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (1636 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (264 : ℝ) * a^3 * (c - b)^5 + (128 : ℝ) * a^2 * (b - a)^6 + (384 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1691 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (2742 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (1919 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (612 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (72 : ℝ) * a^2 * (c - b)^6 + (16 : ℝ) * a^1 * (b - a)^7 + (56 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (452 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (990 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (936 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (442 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (100 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (8 : ℝ) * a^1 * (c - b)^7 + (44 : ℝ) * (b - a)^6 * (c - b)^2 + (132 : ℝ) * (b - a)^5 * (c - b)^3 + (159 : ℝ) * (b - a)^4 * (c - b)^4 + (98 : ℝ) * (b - a)^3 * (c - b)^5 + (31 : ℝ) * (b - a)^2 * (c - b)^6 + (4 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^7*b + 4*a^7*c + 3*a^6*b^2 + 10*a^6*b*c + 3*a^6*c^2 - 4*a^5*b^3 + 4*a^5*b^2*c + 4*a^5*b*c^2 - 4*a^5*c^3 - 6*a^4*b^4 - 10*a^4*b^3*c - 10*a^4*b*c^3 - 6*a^4*c^4 - 4*a^3*b^5 - 10*a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 10*a^3*b*c^4 - 4*a^3*c^5 + 3*a^2*b^6 + 4*a^2*b^5*c + 2*a^2*b^3*c^3 + 4*a^2*b*c^5 + 3*a^2*c^6 + 4*a*b^7 + 10*a*b^6*c + 4*a*b^5*c^2 - 10*a*b^4*c^3 - 10*a*b^3*c^4 + 4*a*b^2*c^5 + 10*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 3*b^6*c^2 - 4*b^5*c^3 - 6*b^4*c^4 - 4*b^3*c^5 + 3*b^2*c^6 + 4*b*c^7) := by
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
  have hn : 0 ≤ (4*a^7*b + 4*a^7*c + 3*a^6*b^2 + 10*a^6*b*c + 3*a^6*c^2 - 4*a^5*b^3 + 4*a^5*b^2*c + 4*a^5*b*c^2 - 4*a^5*c^3 - 6*a^4*b^4 - 10*a^4*b^3*c - 10*a^4*b*c^3 - 6*a^4*c^4 - 4*a^3*b^5 - 10*a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 10*a^3*b*c^4 - 4*a^3*c^5 + 3*a^2*b^6 + 4*a^2*b^5*c + 2*a^2*b^3*c^3 + 4*a^2*b*c^5 + 3*a^2*c^6 + 4*a*b^7 + 10*a*b^6*c + 4*a*b^5*c^2 - 10*a*b^4*c^3 - 10*a*b^3*c^4 + 4*a*b^2*c^5 + 10*a*b*c^6 + 4*a*c^7 + 4*b^7*c + 3*b^6*c^2 - 4*b^5*c^3 - 6*b^4*c^4 - 4*b^3*c^5 + 3*b^2*c^6 + 4*b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 + 3 ≥ 5 * (a + b + c) ^ 2 / (4 * (a * b + b * c + a * c))) := @solution
#print axioms solution
