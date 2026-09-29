-- Prove2me | solution 1 for WorkbookSource.base_28871
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:08:55.75577+00:00
-- url     : https://prove2.me/submissions/d845246e-093d-4e71-89cc-762e16075022

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (b + c) + b^3 / (c + a) + c^3 / (a + b) + 9 * a * b * c * (a + b + c) / (a^2 + b^2 + c^2 + a * b + b * c + c * a) ) ≥ 2 * (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7 + 2*a^6*b + 2*a^6*c - 3*a^4*b^3 - 2*a^4*b^2*c - 2*a^4*b*c^2 - 3*a^4*c^3 - 3*a^3*b^4 + 5*a^3*b^2*c^2 - 3*a^3*c^4 - 2*a^2*b^4*c + 5*a^2*b^3*c^2 + 5*a^2*b^2*c^3 - 2*a^2*b*c^4 + 2*a*b^6 - 2*a*b^4*c^2 - 2*a*b^2*c^4 + 2*a*c^6 + b^7 + 2*b^6*c - 3*b^4*c^3 - 3*b^3*c^4 + 2*b*c^6 + c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^5 * (b - a)^2 + (24 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^5 * (c - b)^2 + (46 : ℝ) * a^4 * (b - a)^3 + (69 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (171 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (74 : ℝ) * a^4 * (c - b)^3 + (29 : ℝ) * a^3 * (b - a)^4 + (58 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (347 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (318 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (85 : ℝ) * a^3 * (c - b)^4 + (6 : ℝ) * a^2 * (b - a)^5 + (15 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (312 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (453 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (240 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (45 : ℝ) * a^2 * (c - b)^5 + (136 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (272 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (214 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (78 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (11 : ℝ) * a^1 * (c - b)^6 + (24 : ℝ) * (b - a)^5 * (c - b)^2 + (60 : ℝ) * (b - a)^4 * (c - b)^3 + (62 : ℝ) * (b - a)^3 * (c - b)^4 + (33 : ℝ) * (b - a)^2 * (c - b)^5 + (9 : ℝ) * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7 + 2*a^6*b + 2*a^6*c - 3*a^4*b^3 - 2*a^4*b^2*c - 2*a^4*b*c^2 - 3*a^4*c^3 - 3*a^3*b^4 + 5*a^3*b^2*c^2 - 3*a^3*c^4 - 2*a^2*b^4*c + 5*a^2*b^3*c^2 + 5*a^2*b^2*c^3 - 2*a^2*b*c^4 + 2*a*b^6 - 2*a*b^4*c^2 - 2*a*b^2*c^4 + 2*a*c^6 + b^7 + 2*b^6*c - 3*b^4*c^3 - 3*b^3*c^4 + 2*b*c^6 + c^7) := by
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
  have hn : 0 ≤ ((a + b + c)*(a^6 + a^5*b + a^5*c - a^4*b^2 - 2*a^4*b*c - a^4*c^2 - 2*a^3*b^3 + a^3*b^2*c + a^3*b*c^2 - 2*a^3*c^3 - a^2*b^4 + a^2*b^3*c + 3*a^2*b^2*c^2 + a^2*b*c^3 - a^2*c^4 + a*b^5 - 2*a*b^4*c + a*b^3*c^2 + a*b^2*c^3 - 2*a*b*c^4 + a*c^5 + b^6 + b^5*c - b^4*c^2 - 2*b^3*c^3 - b^2*c^4 + b*c^5 + c^6)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 / (b + c) + b^3 / (c + a) + c^3 / (a + b) + 9 * a * b * c * (a + b + c) / (a^2 + b^2 + c^2 + a * b + b * c + c * a) ) ≥ 2 * (a * b + b * c + c * a)) := @solution
#print axioms solution
