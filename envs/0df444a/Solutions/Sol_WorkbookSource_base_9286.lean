-- Prove2me | solution 1 for WorkbookSource.base_9286
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:44:16.709799+00:00
-- url     : https://prove2.me/submissions/20b0a1fa-a649-46c3-b1cc-4eef2d7ac5cc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 - b * c) / (b^2 + c^2) + (b^2 - c * a) / (c^2 + a^2) + (c^2 - a * b) / (a^2 + b^2) ≥ 3 * (1 - (a * b + b * c + c * a) / (a^2 + b^2 + c^2))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^8 - a^6*b^2 - a^6*b*c - a^6*c^2 + 2*a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 + 2*a^5*c^3 - 4*a^4*b^4 + a^4*b^3*c - 7*a^4*b^2*c^2 + a^4*b*c^3 - 4*a^4*c^4 + 2*a^3*b^5 + a^3*b^4*c + 3*a^3*b^3*c^2 + 3*a^3*b^2*c^3 + a^3*b*c^4 + 2*a^3*c^5 - a^2*b^6 + 2*a^2*b^5*c - 7*a^2*b^4*c^2 + 3*a^2*b^3*c^3 - 7*a^2*b^2*c^4 + 2*a^2*b*c^5 - a^2*c^6 - a*b^6*c + 2*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 + 2*a*b^2*c^5 - a*b*c^6 + b^8 - b^6*c^2 + 2*b^5*c^3 - 4*b^4*c^4 + 2*b^3*c^5 - b^2*c^6 + c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^6 * (b - a)^2 + (12 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^6 * (c - b)^2 + (36 : ℝ) * a^5 * (b - a)^3 + (54 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (90 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (36 : ℝ) * a^5 * (c - b)^3 + (52 : ℝ) * a^4 * (b - a)^4 + (104 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (246 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (194 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (52 : ℝ) * a^4 * (c - b)^4 + (42 : ℝ) * a^3 * (b - a)^5 + (105 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (338 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (402 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (219 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (46 : ℝ) * a^3 * (c - b)^5 + (19 : ℝ) * a^2 * (b - a)^6 + (57 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (255 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (415 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (342 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (144 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (25 : ℝ) * a^2 * (c - b)^6 + (4 : ℝ) * a^1 * (b - a)^7 + (14 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (100 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (215 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (240 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (152 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (53 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (8 : ℝ) * a^1 * (c - b)^7 + (14 : ℝ) * (b - a)^6 * (c - b)^2 + (42 : ℝ) * (b - a)^5 * (c - b)^3 + (61 : ℝ) * (b - a)^4 * (c - b)^4 + (52 : ℝ) * (b - a)^3 * (c - b)^5 + (27 : ℝ) * (b - a)^2 * (c - b)^6 + (8 : ℝ) * (b - a)^1 * (c - b)^7 + (1 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^8 - a^6*b^2 - a^6*b*c - a^6*c^2 + 2*a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 + 2*a^5*c^3 - 4*a^4*b^4 + a^4*b^3*c - 7*a^4*b^2*c^2 + a^4*b*c^3 - 4*a^4*c^4 + 2*a^3*b^5 + a^3*b^4*c + 3*a^3*b^3*c^2 + 3*a^3*b^2*c^3 + a^3*b*c^4 + 2*a^3*c^5 - a^2*b^6 + 2*a^2*b^5*c - 7*a^2*b^4*c^2 + 3*a^2*b^3*c^3 - 7*a^2*b^2*c^4 + 2*a^2*b*c^5 - a^2*c^6 - a*b^6*c + 2*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 + 2*a*b^2*c^5 - a*b*c^6 + b^8 - b^6*c^2 + 2*b^5*c^3 - 4*b^4*c^4 + 2*b^3*c^5 - b^2*c^6 + c^8) := by
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
  have hn : 0 ≤ (a^8 - a^6*b^2 - a^6*b*c - a^6*c^2 + 2*a^5*b^3 + 2*a^5*b^2*c + 2*a^5*b*c^2 + 2*a^5*c^3 - 4*a^4*b^4 + a^4*b^3*c - 7*a^4*b^2*c^2 + a^4*b*c^3 - 4*a^4*c^4 + 2*a^3*b^5 + a^3*b^4*c + 3*a^3*b^3*c^2 + 3*a^3*b^2*c^3 + a^3*b*c^4 + 2*a^3*c^5 - a^2*b^6 + 2*a^2*b^5*c - 7*a^2*b^4*c^2 + 3*a^2*b^3*c^3 - 7*a^2*b^2*c^4 + 2*a^2*b*c^5 - a^2*c^6 - a*b^6*c + 2*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 + 2*a*b^2*c^5 - a*b*c^6 + b^8 - b^6*c^2 + 2*b^5*c^3 - 4*b^4*c^4 + 2*b^3*c^5 - b^2*c^6 + c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 - b * c) / (b^2 + c^2) + (b^2 - c * a) / (c^2 + a^2) + (c^2 - a * b) / (a^2 + b^2) ≥ 3 * (1 - (a * b + b * c + c * a) / (a^2 + b^2 + c^2))) := @solution
#print axioms solution
