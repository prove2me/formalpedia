-- Prove2me | solution 1 for WorkbookSource.plus_77563
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:29.566615+00:00
-- url     : https://prove2.me/submissions/97c95ed9-b07c-4a27-a935-0b2eb4121588

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2) / (a^2 + a * b + b^2) + (b^2 + c^2) / (b^2 + b * c + c^2) + (c^2 + a^2) / (c^2 + c * a + a^2) ≤ 6 * (a^2 + b^2 + c^2) / (a + b + c)^2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6*b^2 + 4*a^6*b*c + 3*a^6*c^2 - 2*a^5*b^3 - a^5*b^2*c - a^5*b*c^2 - 2*a^5*c^3 + 2*a^4*b^4 - 3*a^4*b^3*c + 2*a^4*b^2*c^2 - 3*a^4*b*c^3 + 2*a^4*c^4 - 2*a^3*b^5 - 3*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 3*a^3*b*c^4 - 2*a^3*c^5 + 3*a^2*b^6 - a^2*b^5*c + 2*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 2*a^2*b^2*c^4 - a^2*b*c^5 + 3*a^2*c^6 + 4*a*b^6*c - a*b^5*c^2 - 3*a*b^4*c^3 - 3*a*b^3*c^4 - a*b^2*c^5 + 4*a*b*c^6 + 3*b^6*c^2 - 2*b^5*c^3 + 2*b^4*c^4 - 2*b^3*c^5 + 3*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (54 : ℝ) * a^6 * (b - a)^2 + (54 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (54 : ℝ) * a^6 * (c - b)^2 + (198 : ℝ) * a^5 * (b - a)^3 + (297 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (351 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (126 : ℝ) * a^5 * (c - b)^3 + (300 : ℝ) * a^4 * (b - a)^4 + (600 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (855 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (555 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (120 : ℝ) * a^4 * (c - b)^4 + (246 : ℝ) * a^3 * (b - a)^5 + (615 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1026 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (924 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (375 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (54 : ℝ) * a^3 * (c - b)^5 + (118 : ℝ) * a^2 * (b - a)^6 + (354 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (663 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (736 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (420 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (111 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (10 : ℝ) * a^2 * (c - b)^6 + (32 : ℝ) * a^1 * (b - a)^7 + (112 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (226 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (285 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (200 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (71 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * (b - a)^8 + (16 : ℝ) * (b - a)^7 * (c - b)^1 + (34 : ℝ) * (b - a)^6 * (c - b)^2 + (46 : ℝ) * (b - a)^5 * (c - b)^3 + (37 : ℝ) * (b - a)^4 * (c - b)^4 + (16 : ℝ) * (b - a)^3 * (c - b)^5 + (3 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6*b^2 + 4*a^6*b*c + 3*a^6*c^2 - 2*a^5*b^3 - a^5*b^2*c - a^5*b*c^2 - 2*a^5*c^3 + 2*a^4*b^4 - 3*a^4*b^3*c + 2*a^4*b^2*c^2 - 3*a^4*b*c^3 + 2*a^4*c^4 - 2*a^3*b^5 - 3*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 3*a^3*b*c^4 - 2*a^3*c^5 + 3*a^2*b^6 - a^2*b^5*c + 2*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 2*a^2*b^2*c^4 - a^2*b*c^5 + 3*a^2*c^6 + 4*a*b^6*c - a*b^5*c^2 - 3*a*b^4*c^3 - 3*a*b^3*c^4 - a*b^2*c^5 + 4*a*b*c^6 + 3*b^6*c^2 - 2*b^5*c^3 + 2*b^4*c^4 - 2*b^3*c^5 + 3*b^2*c^6) := by
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
  have hn : 0 ≤ (3*a^6*b^2 + 4*a^6*b*c + 3*a^6*c^2 - 2*a^5*b^3 - a^5*b^2*c - a^5*b*c^2 - 2*a^5*c^3 + 2*a^4*b^4 - 3*a^4*b^3*c + 2*a^4*b^2*c^2 - 3*a^4*b*c^3 + 2*a^4*c^4 - 2*a^3*b^5 - 3*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 3*a^3*b*c^4 - 2*a^3*c^5 + 3*a^2*b^6 - a^2*b^5*c + 2*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 2*a^2*b^2*c^4 - a^2*b*c^5 + 3*a^2*c^6 + 4*a*b^6*c - a*b^5*c^2 - 3*a*b^4*c^3 - 3*a*b^3*c^4 - a*b^2*c^5 + 4*a*b*c^6 + 3*b^6*c^2 - 2*b^5*c^3 + 2*b^4*c^4 - 2*b^3*c^5 + 3*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2) / (a^2 + a * b + b^2) + (b^2 + c^2) / (b^2 + b * c + c^2) + (c^2 + a^2) / (c^2 + c * a + a^2) ≤ 6 * (a^2 + b^2 + c^2) / (a + b + c)^2) := @solution
#print axioms solution
