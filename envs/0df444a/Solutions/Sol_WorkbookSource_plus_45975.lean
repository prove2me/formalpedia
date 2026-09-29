-- Prove2me | solution 1 for WorkbookSource.plus_45975
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:16:59.688726+00:00
-- url     : https://prove2.me/submissions/dd0a39a9-50a9-45a8-9f56-f1b6ceeb0e5c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c + 2 * a) / (a ^ 2 + 2 * b * c) + b * (c + a + 2 * b) / (b ^ 2 + 2 * c * a) + c * (a + b + 2 * c) / (c ^ 2 + 2 * a * b)) ≥ 3 + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6*b^2 - 4*a^6*b*c + 2*a^6*c^2 + 2*a^5*b^3 + 3*a^5*b^2*c + 3*a^5*b*c^2 + 2*a^5*c^3 + 2*a^4*b^4 + a^4*b^3*c - 21*a^4*b^2*c^2 + a^4*b*c^3 + 2*a^4*c^4 + 2*a^3*b^5 + a^3*b^4*c + 7*a^3*b^3*c^2 + 7*a^3*b^2*c^3 + a^3*b*c^4 + 2*a^3*c^5 + 2*a^2*b^6 + 3*a^2*b^5*c - 21*a^2*b^4*c^2 + 7*a^2*b^3*c^3 - 21*a^2*b^2*c^4 + 3*a^2*b*c^5 + 2*a^2*c^6 - 4*a*b^6*c + 3*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 + 3*a*b^2*c^5 - 4*a*b*c^6 + 2*b^6*c^2 + 2*b^5*c^3 + 2*b^4*c^4 + 2*b^3*c^5 + 2*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (45 : ℝ) * a^6 * (b - a)^2 + (45 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (45 : ℝ) * a^6 * (c - b)^2 + (210 : ℝ) * a^5 * (b - a)^3 + (315 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (225 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (60 : ℝ) * a^5 * (c - b)^3 + (410 : ℝ) * a^4 * (b - a)^4 + (820 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (630 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (220 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (35 : ℝ) * a^4 * (c - b)^4 + (430 : ℝ) * a^3 * (b - a)^5 + (1075 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1010 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (440 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (95 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (10 : ℝ) * a^3 * (c - b)^5 + (255 : ℝ) * a^2 * (b - a)^6 + (765 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (894 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (513 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (144 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (15 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (80 : ℝ) * a^1 * (b - a)^7 + (280 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (402 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (305 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (124 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (21 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (10 : ℝ) * (b - a)^8 + (40 : ℝ) * (b - a)^7 * (c - b)^1 + (70 : ℝ) * (b - a)^6 * (c - b)^2 + (70 : ℝ) * (b - a)^5 * (c - b)^3 + (42 : ℝ) * (b - a)^4 * (c - b)^4 + (14 : ℝ) * (b - a)^3 * (c - b)^5 + (2 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6*b^2 - 4*a^6*b*c + 2*a^6*c^2 + 2*a^5*b^3 + 3*a^5*b^2*c + 3*a^5*b*c^2 + 2*a^5*c^3 + 2*a^4*b^4 + a^4*b^3*c - 21*a^4*b^2*c^2 + a^4*b*c^3 + 2*a^4*c^4 + 2*a^3*b^5 + a^3*b^4*c + 7*a^3*b^3*c^2 + 7*a^3*b^2*c^3 + a^3*b*c^4 + 2*a^3*c^5 + 2*a^2*b^6 + 3*a^2*b^5*c - 21*a^2*b^4*c^2 + 7*a^2*b^3*c^3 - 21*a^2*b^2*c^4 + 3*a^2*b*c^5 + 2*a^2*c^6 - 4*a*b^6*c + 3*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 + 3*a*b^2*c^5 - 4*a*b*c^6 + 2*b^6*c^2 + 2*b^5*c^3 + 2*b^4*c^4 + 2*b^3*c^5 + 2*b^2*c^6) := by
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
  have hn : 0 ≤ (2*a^6*b^2 - 4*a^6*b*c + 2*a^6*c^2 + 2*a^5*b^3 + 3*a^5*b^2*c + 3*a^5*b*c^2 + 2*a^5*c^3 + 2*a^4*b^4 + a^4*b^3*c - 21*a^4*b^2*c^2 + a^4*b*c^3 + 2*a^4*c^4 + 2*a^3*b^5 + a^3*b^4*c + 7*a^3*b^3*c^2 + 7*a^3*b^2*c^3 + a^3*b*c^4 + 2*a^3*c^5 + 2*a^2*b^6 + 3*a^2*b^5*c - 21*a^2*b^4*c^2 + 7*a^2*b^3*c^3 - 21*a^2*b^2*c^4 + 3*a^2*b*c^5 + 2*a^2*c^6 - 4*a*b^6*c + 3*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 + 3*a*b^2*c^5 - 4*a*b*c^6 + 2*b^6*c^2 + 2*b^5*c^3 + 2*b^4*c^4 + 2*b^3*c^5 + 2*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (b + c + 2 * a) / (a ^ 2 + 2 * b * c) + b * (c + a + 2 * b) / (b ^ 2 + 2 * c * a) + c * (a + b + 2 * c) / (c ^ 2 + 2 * a * b)) ≥ 3 + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
