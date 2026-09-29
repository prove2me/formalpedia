-- Prove2me | solution 1 for WorkbookSource.base_56441
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:42:04.591636+00:00
-- url     : https://prove2.me/submissions/359437e7-4907-4f29-a119-0049ec86909b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (a * b * c) + 4 * ((a * b + b * c + c * a) / (a^2 + b^2 + c^2))^2 ≥ 7  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7 + 2*a^5*b^2 - 7*a^5*b*c + 2*a^5*c^2 + a^4*b^3 + a^4*c^3 + a^3*b^4 - 10*a^3*b^3*c + 10*a^3*b^2*c^2 - 10*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^5 + 10*a^2*b^3*c^2 + 10*a^2*b^2*c^3 + 2*a^2*c^5 - 7*a*b^5*c - 10*a*b^3*c^3 - 7*a*b*c^5 + b^7 + 2*b^5*c^2 + b^4*c^3 + b^3*c^4 + 2*b^2*c^5 + c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^5 * (b - a)^2 + (3 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^5 * (c - b)^2 + (10 : ℝ) * a^4 * (b - a)^3 + (15 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (15 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (5 : ℝ) * a^4 * (c - b)^3 + (32 : ℝ) * a^3 * (b - a)^4 + (64 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (86 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (54 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (22 : ℝ) * a^3 * (c - b)^4 + (48 : ℝ) * a^2 * (b - a)^5 + (120 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (180 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (150 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (78 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * a^2 * (c - b)^5 + (32 : ℝ) * a^1 * (b - a)^6 + (96 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (160 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (160 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (103 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (39 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (7 : ℝ) * a^1 * (c - b)^6 + (8 : ℝ) * (b - a)^7 + (28 : ℝ) * (b - a)^6 * (c - b)^1 + (52 : ℝ) * (b - a)^5 * (c - b)^2 + (60 : ℝ) * (b - a)^4 * (c - b)^3 + (46 : ℝ) * (b - a)^3 * (c - b)^4 + (23 : ℝ) * (b - a)^2 * (c - b)^5 + (7 : ℝ) * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7 + 2*a^5*b^2 - 7*a^5*b*c + 2*a^5*c^2 + a^4*b^3 + a^4*c^3 + a^3*b^4 - 10*a^3*b^3*c + 10*a^3*b^2*c^2 - 10*a^3*b*c^3 + a^3*c^4 + 2*a^2*b^5 + 10*a^2*b^3*c^2 + 10*a^2*b^2*c^3 + 2*a^2*c^5 - 7*a*b^5*c - 10*a*b^3*c^3 - 7*a*b*c^5 + b^7 + 2*b^5*c^2 + b^4*c^3 + b^3*c^4 + 2*b^2*c^5 + c^7) := by
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
  have hn : 0 ≤ ((a^2 - a*b - a*c + b^2 - b*c + c^2)*(a^5 + a^4*b + a^4*c + 2*a^3*b^2 - 4*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 2*a^2*b^2*c - 2*a^2*b*c^2 + 2*a^2*c^3 + a*b^4 - 4*a*b^3*c - 2*a*b^2*c^2 - 4*a*b*c^3 + a*c^4 + b^5 + b^4*c + 2*b^3*c^2 + 2*b^2*c^3 + b*c^4 + c^5)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3 + c^3) / (a * b * c) + 4 * ((a * b + b * c + c * a) / (a^2 + b^2 + c^2))^2 ≥ 7) := @solution
#print axioms solution
