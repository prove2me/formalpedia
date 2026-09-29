-- Prove2me | solution 1 for WorkbookSource.base_39288
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:47:25.931247+00:00
-- url     : https://prove2.me/submissions/305093d7-0807-463c-8474-74da327696f1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b * c) / (2 * a + b + c) + (b^2 + c * a) / (a + 2 * b + c) + (c^2 + a * b) / (a + b + 2 * c) ≤ (1 / 2) * (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) + (a + b + c) / 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^7 + 16*a^6*b + 16*a^6*c + 15*a^5*b^2 + 38*a^5*b*c + 15*a^5*c^2 - 11*a^4*b^3 + 3*a^4*b^2*c + 3*a^4*b*c^2 - 11*a^4*c^3 - 11*a^3*b^4 - 38*a^3*b^3*c - 50*a^3*b^2*c^2 - 38*a^3*b*c^3 - 11*a^3*c^4 + 15*a^2*b^5 + 3*a^2*b^4*c - 50*a^2*b^3*c^2 - 50*a^2*b^2*c^3 + 3*a^2*b*c^4 + 15*a^2*c^5 + 16*a*b^6 + 38*a*b^5*c + 3*a*b^4*c^2 - 38*a*b^3*c^3 + 3*a*b^2*c^4 + 38*a*b*c^5 + 16*a*c^6 + 4*b^7 + 16*b^6*c + 15*b^5*c^2 - 11*b^4*c^3 - 11*b^3*c^4 + 15*b^2*c^5 + 16*b*c^6 + 4*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (640 : ℝ) * a^5 * (b - a)^2 + (640 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (640 : ℝ) * a^5 * (c - b)^2 + (1952 : ℝ) * a^4 * (b - a)^3 + (2928 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (3472 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (1248 : ℝ) * a^4 * (c - b)^3 + (2352 : ℝ) * a^3 * (b - a)^4 + (4704 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (6736 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (4384 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (944 : ℝ) * a^3 * (c - b)^4 + (1400 : ℝ) * a^2 * (b - a)^5 + (3500 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (5976 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (5464 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (2276 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (344 : ℝ) * a^2 * (c - b)^5 + (412 : ℝ) * a^1 * (b - a)^6 + (1236 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (2477 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (2894 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (1765 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (524 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (60 : ℝ) * a^1 * (c - b)^6 + (48 : ℝ) * (b - a)^7 + (168 : ℝ) * (b - a)^6 * (c - b)^1 + (390 : ℝ) * (b - a)^5 * (c - b)^2 + (555 : ℝ) * (b - a)^4 * (c - b)^3 + (444 : ℝ) * (b - a)^3 * (c - b)^4 + (195 : ℝ) * (b - a)^2 * (c - b)^5 + (44 : ℝ) * (b - a)^1 * (c - b)^6 + (4 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^7 + 16*a^6*b + 16*a^6*c + 15*a^5*b^2 + 38*a^5*b*c + 15*a^5*c^2 - 11*a^4*b^3 + 3*a^4*b^2*c + 3*a^4*b*c^2 - 11*a^4*c^3 - 11*a^3*b^4 - 38*a^3*b^3*c - 50*a^3*b^2*c^2 - 38*a^3*b*c^3 - 11*a^3*c^4 + 15*a^2*b^5 + 3*a^2*b^4*c - 50*a^2*b^3*c^2 - 50*a^2*b^2*c^3 + 3*a^2*b*c^4 + 15*a^2*c^5 + 16*a*b^6 + 38*a*b^5*c + 3*a*b^4*c^2 - 38*a*b^3*c^3 + 3*a*b^2*c^4 + 38*a*b*c^5 + 16*a*c^6 + 4*b^7 + 16*b^6*c + 15*b^5*c^2 - 11*b^4*c^3 - 11*b^3*c^4 + 15*b^2*c^5 + 16*b*c^6 + 4*c^7) := by
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
  have hn : 0 ≤ (4*a^7 + 16*a^6*b + 16*a^6*c + 15*a^5*b^2 + 38*a^5*b*c + 15*a^5*c^2 - 11*a^4*b^3 + 3*a^4*b^2*c + 3*a^4*b*c^2 - 11*a^4*c^3 - 11*a^3*b^4 - 38*a^3*b^3*c - 50*a^3*b^2*c^2 - 38*a^3*b*c^3 - 11*a^3*c^4 + 15*a^2*b^5 + 3*a^2*b^4*c - 50*a^2*b^3*c^2 - 50*a^2*b^2*c^3 + 3*a^2*b*c^4 + 15*a^2*c^5 + 16*a*b^6 + 38*a*b^5*c + 3*a*b^4*c^2 - 38*a*b^3*c^3 + 3*a*b^2*c^4 + 38*a*b*c^5 + 16*a*c^6 + 4*b^7 + 16*b^6*c + 15*b^5*c^2 - 11*b^4*c^3 - 11*b^3*c^4 + 15*b^2*c^5 + 16*b*c^6 + 4*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b * c) / (2 * a + b + c) + (b^2 + c * a) / (a + 2 * b + c) + (c^2 + a * b) / (a + b + 2 * c) ≤ (1 / 2) * (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) + (a + b + c) / 2)) := @solution
#print axioms solution
