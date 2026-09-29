-- Prove2me | solution 1 for WorkbookSource.base_9008
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:40:42.566771+00:00
-- url     : https://prove2.me/submissions/4595d05d-e055-4c9d-91d7-b086a3483f33

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a + b) ^ 2 + 1 / (a + c) ^ 2 + 8 / (b + c) ^ 2) ≥ 4 / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^5*b + 8*a^5*c + 12*a^4*b^2 + 32*a^4*b*c + 12*a^4*c^2 + 2*a^3*b^3 + 38*a^3*b^2*c + 38*a^3*b*c^2 + 2*a^3*c^3 - 2*a^2*b^4 + 10*a^2*b^3*c + 40*a^2*b^2*c^2 + 10*a^2*b*c^3 - 2*a^2*c^4 + a*b^5 - 3*a*b^4*c + 10*a*b^3*c^2 + 10*a*b^2*c^3 - 3*a*b*c^4 + a*c^5 + b^5*c - 2*b^4*c^2 + 2*b^3*c^3 - 2*b^2*c^4 + b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (224 : ℝ) * a^6 + (672 : ℝ) * a^5 * (b - a)^1 + (336 : ℝ) * a^5 * (c - b)^1 + (792 : ℝ) * a^4 * (b - a)^2 + (792 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (148 : ℝ) * a^4 * (c - b)^2 + (464 : ℝ) * a^3 * (b - a)^3 + (696 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (264 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (16 : ℝ) * a^3 * (c - b)^3 + (136 : ℝ) * a^2 * (b - a)^4 + (272 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (166 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (30 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (3 : ℝ) * a^2 * (c - b)^4 + (16 : ℝ) * a^1 * (b - a)^5 + (40 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (40 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (20 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (8 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (2 : ℝ) * (b - a)^4 * (c - b)^2 + (4 : ℝ) * (b - a)^3 * (c - b)^3 + (3 : ℝ) * (b - a)^2 * (c - b)^4 + (1 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ a) (hord2 : a ≤ c) : 0 ≤ (8*a^5*b + 8*a^5*c + 12*a^4*b^2 + 32*a^4*b*c + 12*a^4*c^2 + 2*a^3*b^3 + 38*a^3*b^2*c + 38*a^3*b*c^2 + 2*a^3*c^3 - 2*a^2*b^4 + 10*a^2*b^3*c + 40*a^2*b^2*c^2 + 10*a^2*b*c^3 - 2*a^2*c^4 + a*b^5 - 3*a*b^4*c + 10*a*b^3*c^2 + 10*a*b^2*c^3 - 3*a*b*c^4 + a*c^5 + b^5*c - 2*b^4*c^2 + 2*b^3*c^3 - 2*b^2*c^4 + b*c^5) := by
    have hdiff1 : 0 ≤ (a - b) := by linarith
    have hdiff2 : 0 ≤ (c - a) := by linarith
    have hpos : 0 ≤ (224 : ℝ) * b^6 + (1008 : ℝ) * b^5 * (a - b)^1 + (336 : ℝ) * b^5 * (c - a)^1 + (1828 : ℝ) * b^4 * (a - b)^2 + (1184 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (148 : ℝ) * b^4 * (c - a)^2 + (1696 : ℝ) * b^3 * (a - b)^3 + (1592 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (376 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (16 : ℝ) * b^3 * (c - a)^3 + (843 : ℝ) * b^2 * (a - b)^4 + (1014 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (334 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (30 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (3 : ℝ) * b^2 * (c - a)^4 + (212 : ℝ) * b^1 * (a - b)^5 + (306 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (124 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (20 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (8 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (2 : ℝ) * b^1 * (c - a)^5 + (21 : ℝ) * (a - b)^6 + (35 : ℝ) * (a - b)^5 * (c - a)^1 + (16 : ℝ) * (a - b)^4 * (c - a)^2 + (4 : ℝ) * (a - b)^3 * (c - a)^3 + (3 : ℝ) * (a - b)^2 * (c - a)^4 + (1 : ℝ) * (a - b)^1 * (c - a)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ c) (hord2 : c ≤ a) : 0 ≤ (8*a^5*b + 8*a^5*c + 12*a^4*b^2 + 32*a^4*b*c + 12*a^4*c^2 + 2*a^3*b^3 + 38*a^3*b^2*c + 38*a^3*b*c^2 + 2*a^3*c^3 - 2*a^2*b^4 + 10*a^2*b^3*c + 40*a^2*b^2*c^2 + 10*a^2*b*c^3 - 2*a^2*c^4 + a*b^5 - 3*a*b^4*c + 10*a*b^3*c^2 + 10*a*b^2*c^3 - 3*a*b*c^4 + a*c^5 + b^5*c - 2*b^4*c^2 + 2*b^3*c^3 - 2*b^2*c^4 + b*c^5) := by
    have hdiff1 : 0 ≤ (c - b) := by linarith
    have hdiff2 : 0 ≤ (a - c) := by linarith
    have hpos : 0 ≤ (224 : ℝ) * b^6 + (1008 : ℝ) * b^5 * (c - b)^1 + (672 : ℝ) * b^5 * (a - c)^1 + (1828 : ℝ) * b^4 * (c - b)^2 + (2472 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (792 : ℝ) * b^4 * (a - c)^2 + (1696 : ℝ) * b^3 * (c - b)^3 + (3496 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (2280 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (464 : ℝ) * b^3 * (a - c)^3 + (843 : ℝ) * b^2 * (c - b)^4 + (2358 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (2350 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (968 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (136 : ℝ) * b^2 * (a - c)^4 + (212 : ℝ) * b^1 * (c - b)^5 + (754 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (1020 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (636 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (176 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (16 : ℝ) * b^1 * (a - c)^5 + (21 : ℝ) * (c - b)^6 + (91 : ℝ) * (c - b)^5 * (a - c)^1 + (156 : ℝ) * (c - b)^4 * (a - c)^2 + (130 : ℝ) * (c - b)^3 * (a - c)^3 + (52 : ℝ) * (c - b)^2 * (a - c)^4 + (8 : ℝ) * (c - b)^1 * (a - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^5*b + 8*a^5*c + 12*a^4*b^2 + 32*a^4*b*c + 12*a^4*c^2 + 2*a^3*b^3 + 38*a^3*b^2*c + 38*a^3*b*c^2 + 2*a^3*c^3 - 2*a^2*b^4 + 10*a^2*b^3*c + 40*a^2*b^2*c^2 + 10*a^2*b*c^3 - 2*a^2*c^4 + a*b^5 - 3*a*b^4*c + 10*a*b^3*c^2 + 10*a*b^2*c^3 - 3*a*b*c^4 + a*c^5 + b^5*c - 2*b^4*c^2 + 2*b^3*c^3 - 2*b^2*c^4 + b*c^5) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (8*a^5*b + 8*a^5*c + 12*a^4*b^2 + 32*a^4*b*c + 12*a^4*c^2 + 2*a^3*b^3 + 38*a^3*b^2*c + 38*a^3*b*c^2 + 2*a^3*c^3 - 2*a^2*b^4 + 10*a^2*b^3*c + 40*a^2*b^2*c^2 + 10*a^2*b*c^3 - 2*a^2*c^4 + a*b^5 - 3*a*b^4*c + 10*a*b^3*c^2 + 10*a*b^2*c^3 - 3*a*b*c^4 + a*c^5 + b^5*c - 2*b^4*c^2 + 2*b^3*c^3 - 2*b^2*c^4 + b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (a + b) ^ 2 + 1 / (a + c) ^ 2 + 8 / (b + c) ^ 2) ≥ 4 / (a * b + b * c + c * a)) := @solution
#print axioms solution
