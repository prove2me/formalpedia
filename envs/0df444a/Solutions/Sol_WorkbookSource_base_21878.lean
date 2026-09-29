-- Prove2me | solution 1 for WorkbookSource.base_21878
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:51:00.648+00:00
-- url     : https://prove2.me/submissions/f3ae6938-53ad-4b94-aafc-f18021c2fb32

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * (b + c)^2 / (a^2 + b * c) + b^2 * (c + a)^2 / (b^2 + c * a) + c^2 * (a + b)^2 / (c^2 + a * b)) ≤ a^2 + b^2 + c^2 + a * b + b * c + c * a  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b*c + a^5*b^2*c + a^5*b*c^2 + a^4*b^4 - a^4*b^3*c - a^4*b^2*c^2 - a^4*b*c^3 + a^4*c^4 - a^3*b^4*c - a^3*b^3*c^2 - a^3*b^2*c^3 - a^3*b*c^4 + a^2*b^5*c - a^2*b^4*c^2 - a^2*b^3*c^3 - a^2*b^2*c^4 + a^2*b*c^5 + a*b^6*c + a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + a*b^2*c^5 + a*b*c^6 + b^4*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^6 * (b - a)^2 + (16 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^6 * (c - b)^2 + (64 : ℝ) * a^5 * (b - a)^3 + (96 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (96 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (32 : ℝ) * a^5 * (c - b)^3 + (104 : ℝ) * a^4 * (b - a)^4 + (208 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (232 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (128 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (24 : ℝ) * a^4 * (c - b)^4 + (88 : ℝ) * a^3 * (b - a)^5 + (220 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (280 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (200 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (68 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (8 : ℝ) * a^3 * (c - b)^5 + (41 : ℝ) * a^2 * (b - a)^6 + (123 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (175 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (145 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (67 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (15 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^2 * (c - b)^6 + (10 : ℝ) * a^1 * (b - a)^7 + (35 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (53 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (45 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (23 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (7 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (1 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (b - a)^8 + (4 : ℝ) * (b - a)^7 * (c - b)^1 + (6 : ℝ) * (b - a)^6 * (c - b)^2 + (4 : ℝ) * (b - a)^5 * (c - b)^3 + (1 : ℝ) * (b - a)^4 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b*c + a^5*b^2*c + a^5*b*c^2 + a^4*b^4 - a^4*b^3*c - a^4*b^2*c^2 - a^4*b*c^3 + a^4*c^4 - a^3*b^4*c - a^3*b^3*c^2 - a^3*b^2*c^3 - a^3*b*c^4 + a^2*b^5*c - a^2*b^4*c^2 - a^2*b^3*c^3 - a^2*b^2*c^4 + a^2*b*c^5 + a*b^6*c + a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + a*b^2*c^5 + a*b*c^6 + b^4*c^4) := by
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
  have hn : 0 ≤ (a^6*b*c + a^5*b^2*c + a^5*b*c^2 + a^4*b^4 - a^4*b^3*c - a^4*b^2*c^2 - a^4*b*c^3 + a^4*c^4 - a^3*b^4*c - a^3*b^3*c^2 - a^3*b^2*c^3 - a^3*b*c^4 + a^2*b^5*c - a^2*b^4*c^2 - a^2*b^3*c^3 - a^2*b^2*c^4 + a^2*b*c^5 + a*b^6*c + a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + a*b^2*c^5 + a*b*c^6 + b^4*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 * (b + c)^2 / (a^2 + b * c) + b^2 * (c + a)^2 / (b^2 + c * a) + c^2 * (a + b)^2 / (c^2 + a * b)) ≤ a^2 + b^2 + c^2 + a * b + b * c + c * a) := @solution
#print axioms solution
