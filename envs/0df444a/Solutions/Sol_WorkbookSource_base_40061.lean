-- Prove2me | solution 1 for WorkbookSource.base_40061
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:37.617556+00:00
-- url     : https://prove2.me/submissions/3317cc20-ee40-45e1-ae65-3bb2592c35fa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a * b + b * c + c * a) ^ 4 ≥ a ^ 2 * b ^ 2 * c ^ 2 * (16 * (a ^ 2 + b ^ 2 + c ^ 2) + 11 * (a * b + b * c + c * a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^4 + 4*a^4*b^3*c - 10*a^4*b^2*c^2 + 4*a^4*b*c^3 + a^4*c^4 + 4*a^3*b^4*c + a^3*b^3*c^2 + a^3*b^2*c^3 + 4*a^3*b*c^4 - 10*a^2*b^4*c^2 + a^2*b^3*c^3 - 10*a^2*b^2*c^4 + 4*a*b^4*c^3 + 4*a*b^3*c^4 + b^4*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (11 : ℝ) * a^6 * (b - a)^2 + (11 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (11 : ℝ) * a^6 * (c - b)^2 + (56 : ℝ) * a^5 * (b - a)^3 + (84 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (48 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (10 : ℝ) * a^5 * (c - b)^3 + (115 : ℝ) * a^4 * (b - a)^4 + (230 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (140 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (25 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (120 : ℝ) * a^3 * (b - a)^5 + (300 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (240 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (60 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (65 : ℝ) * a^2 * (b - a)^6 + (195 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (203 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (81 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (8 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (16 : ℝ) * a^1 * (b - a)^7 + (56 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (72 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (40 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (8 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (1 : ℝ) * (b - a)^8 + (4 : ℝ) * (b - a)^7 * (c - b)^1 + (6 : ℝ) * (b - a)^6 * (c - b)^2 + (4 : ℝ) * (b - a)^5 * (c - b)^3 + (1 : ℝ) * (b - a)^4 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^4 + 4*a^4*b^3*c - 10*a^4*b^2*c^2 + 4*a^4*b*c^3 + a^4*c^4 + 4*a^3*b^4*c + a^3*b^3*c^2 + a^3*b^2*c^3 + 4*a^3*b*c^4 - 10*a^2*b^4*c^2 + a^2*b^3*c^3 - 10*a^2*b^2*c^4 + 4*a*b^4*c^3 + 4*a*b^3*c^4 + b^4*c^4) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), (a * b + b * c + c * a) ^ 4 ≥ a ^ 2 * b ^ 2 * c ^ 2 * (16 * (a ^ 2 + b ^ 2 + c ^ 2) + 11 * (a * b + b * c + c * a))) := @solution
#print axioms solution
