-- Prove2me | solution 1 for WorkbookSource.plus_74571
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:26.942032+00:00
-- url     : https://prove2.me/submissions/f26d6bca-b35c-4d72-a1c3-e9acf5b984c2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 9 * b * c) / (2 * a^2 + (b + c)^2) + (b^2 + 9 * c * a) / (2 * b^2 + (c + a)^2) + (c^2 + 9 * a * b) / (2 * c^2 + (a + b)^2) ≤ 5   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (9*a^6 + 30*a^4*b^2 - 35*a^4*b*c + 30*a^4*c^2 - 3*a^3*b^3 - 15*a^3*b^2*c - 15*a^3*b*c^2 - 3*a^3*c^3 + 30*a^2*b^4 - 15*a^2*b^3*c - 3*a^2*b^2*c^2 - 15*a^2*b*c^3 + 30*a^2*c^4 - 35*a*b^4*c - 15*a*b^3*c^2 - 15*a*b^2*c^3 - 35*a*b*c^4 + 9*b^6 + 30*b^4*c^2 - 3*b^3*c^3 + 30*b^2*c^4 + 9*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (204 : ℝ) * a^4 * (b - a)^2 + (204 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (204 : ℝ) * a^4 * (c - b)^2 + (572 : ℝ) * a^3 * (b - a)^3 + (858 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (774 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (244 : ℝ) * a^3 * (c - b)^3 + (652 : ℝ) * a^2 * (b - a)^4 + (1304 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1338 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (686 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (160 : ℝ) * a^2 * (c - b)^4 + (350 : ℝ) * a^1 * (b - a)^5 + (875 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1074 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (736 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (295 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (54 : ℝ) * a^1 * (c - b)^5 + (75 : ℝ) * (b - a)^6 + (225 : ℝ) * (b - a)^5 * (c - b)^1 + (336 : ℝ) * (b - a)^4 * (c - b)^2 + (297 : ℝ) * (b - a)^3 * (c - b)^3 + (165 : ℝ) * (b - a)^2 * (c - b)^4 + (54 : ℝ) * (b - a)^1 * (c - b)^5 + (9 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (9*a^6 + 30*a^4*b^2 - 35*a^4*b*c + 30*a^4*c^2 - 3*a^3*b^3 - 15*a^3*b^2*c - 15*a^3*b*c^2 - 3*a^3*c^3 + 30*a^2*b^4 - 15*a^2*b^3*c - 3*a^2*b^2*c^2 - 15*a^2*b*c^3 + 30*a^2*c^4 - 35*a*b^4*c - 15*a*b^3*c^2 - 15*a*b^2*c^3 - 35*a*b*c^4 + 9*b^6 + 30*b^4*c^2 - 3*b^3*c^3 + 30*b^2*c^4 + 9*c^6) := by
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
  have hn : 0 ≤ (9*a^6 + 30*a^4*b^2 - 35*a^4*b*c + 30*a^4*c^2 - 3*a^3*b^3 - 15*a^3*b^2*c - 15*a^3*b*c^2 - 3*a^3*c^3 + 30*a^2*b^4 - 15*a^2*b^3*c - 3*a^2*b^2*c^2 - 15*a^2*b*c^3 + 30*a^2*c^4 - 35*a*b^4*c - 15*a*b^3*c^2 - 15*a*b^2*c^3 - 35*a*b*c^4 + 9*b^6 + 30*b^4*c^2 - 3*b^3*c^3 + 30*b^2*c^4 + 9*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + 9 * b * c) / (2 * a^2 + (b + c)^2) + (b^2 + 9 * c * a) / (2 * b^2 + (c + a)^2) + (c^2 + 9 * a * b) / (2 * c^2 + (a + b)^2) ≤ 5) := @solution
#print axioms solution
