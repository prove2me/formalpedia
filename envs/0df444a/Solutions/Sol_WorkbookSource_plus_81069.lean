-- Prove2me | solution 1 for WorkbookSource.plus_81069
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:57:28.79614+00:00
-- url     : https://prove2.me/submissions/48eb5e30-4fa5-44e6-a3bc-0350a0083819

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 / (c * (2 * c + a + b)) + (b + c) ^ 2 / (a * (2 * a + b + c)) + (c + a) ^ 2 / (b * (2 * b + c + a)) ≥ (a + b) / (2 * c) + (b + c) / (2 * a) + (c + a) / (2 * b)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b + 2*a^5*c + 9*a^4*b^2 - 2*a^4*b*c + 9*a^4*c^2 + 14*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 + 14*a^3*c^3 + 9*a^2*b^4 - 12*a^2*b^3*c - 30*a^2*b^2*c^2 - 12*a^2*b*c^3 + 9*a^2*c^4 + 2*a*b^5 - 2*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 - 2*a*b*c^4 + 2*a*c^5 + 2*b^5*c + 9*b^4*c^2 + 14*b^3*c^3 + 9*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (112 : ℝ) * a^4 * (b - a)^2 + (112 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (112 : ℝ) * a^4 * (c - b)^2 + (340 : ℝ) * a^3 * (b - a)^3 + (510 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (386 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (108 : ℝ) * a^3 * (c - b)^3 + (384 : ℝ) * a^2 * (b - a)^4 + (768 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (618 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (234 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (36 : ℝ) * a^2 * (c - b)^4 + (192 : ℝ) * a^1 * (b - a)^5 + (480 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (460 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (210 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (46 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (36 : ℝ) * (b - a)^6 + (108 : ℝ) * (b - a)^5 * (c - b)^1 + (125 : ℝ) * (b - a)^4 * (c - b)^2 + (70 : ℝ) * (b - a)^3 * (c - b)^3 + (19 : ℝ) * (b - a)^2 * (c - b)^4 + (2 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b + 2*a^5*c + 9*a^4*b^2 - 2*a^4*b*c + 9*a^4*c^2 + 14*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 + 14*a^3*c^3 + 9*a^2*b^4 - 12*a^2*b^3*c - 30*a^2*b^2*c^2 - 12*a^2*b*c^3 + 9*a^2*c^4 + 2*a*b^5 - 2*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 - 2*a*b*c^4 + 2*a*c^5 + 2*b^5*c + 9*b^4*c^2 + 14*b^3*c^3 + 9*b^2*c^4 + 2*b*c^5) := by
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
  have hn : 0 ≤ (2*a^5*b + 2*a^5*c + 9*a^4*b^2 - 2*a^4*b*c + 9*a^4*c^2 + 14*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 + 14*a^3*c^3 + 9*a^2*b^4 - 12*a^2*b^3*c - 30*a^2*b^2*c^2 - 12*a^2*b*c^3 + 9*a^2*c^4 + 2*a*b^5 - 2*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 - 2*a*b*c^4 + 2*a*c^5 + 2*b^5*c + 9*b^4*c^2 + 14*b^3*c^3 + 9*b^2*c^4 + 2*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) ^ 2 / (c * (2 * c + a + b)) + (b + c) ^ 2 / (a * (2 * a + b + c)) + (c + a) ^ 2 / (b * (2 * b + c + a)) ≥ (a + b) / (2 * c) + (b + c) / (2 * a) + (c + a) / (2 * b)) := @solution
#print axioms solution
