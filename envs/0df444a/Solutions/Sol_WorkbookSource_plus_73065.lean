-- Prove2me | solution 1 for WorkbookSource.plus_73065
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:22.715233+00:00
-- url     : https://prove2.me/submissions/80bad919-d1ae-4537-9947-b0efac0f5af1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) + (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + 12 / 25 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 27 / 25   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (48*a^8 + 8*a^7*b + 8*a^7*c + 16*a^6*b^2 + 48*a^6*b*c + 16*a^6*c^2 + 24*a^5*b^3 - 88*a^5*b^2*c - 88*a^5*b*c^2 + 24*a^5*c^3 - 64*a^4*b^4 - 48*a^4*b^3*c + 224*a^4*b^2*c^2 - 48*a^4*b*c^3 - 64*a^4*c^4 + 24*a^3*b^5 - 48*a^3*b^4*c - 80*a^3*b^3*c^2 - 80*a^3*b^2*c^3 - 48*a^3*b*c^4 + 24*a^3*c^5 + 16*a^2*b^6 - 88*a^2*b^5*c + 224*a^2*b^4*c^2 - 80*a^2*b^3*c^3 + 224*a^2*b^2*c^4 - 88*a^2*b*c^5 + 16*a^2*c^6 + 8*a*b^7 + 48*a*b^6*c - 88*a*b^5*c^2 - 48*a*b^4*c^3 - 48*a*b^3*c^4 - 88*a*b^2*c^5 + 48*a*b*c^6 + 8*a*c^7 + 48*b^8 + 8*b^7*c + 16*b^6*c^2 + 24*b^5*c^3 - 64*b^4*c^4 + 24*b^3*c^5 + 16*b^2*c^6 + 8*b*c^7 + 48*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1200 : ℝ) * a^6 * (b - a)^2 + (1200 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (1200 : ℝ) * a^6 * (c - b)^2 + (3840 : ℝ) * a^5 * (b - a)^3 + (5760 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (8640 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (3360 : ℝ) * a^5 * (c - b)^3 + (5680 : ℝ) * a^4 * (b - a)^4 + (11360 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (23040 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (17360 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (4480 : ℝ) * a^4 * (c - b)^4 + (4944 : ℝ) * a^3 * (b - a)^5 + (12360 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (31184 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (34416 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (17400 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (3376 : ℝ) * a^3 * (c - b)^5 + (2688 : ℝ) * a^2 * (b - a)^6 + (8064 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (23568 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (33696 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (25176 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (9672 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1536 : ℝ) * a^2 * (c - b)^6 + (864 : ℝ) * a^1 * (b - a)^7 + (3024 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (9664 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (16600 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (16256 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (9296 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2936 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (400 : ℝ) * a^1 * (c - b)^7 + (128 : ℝ) * (b - a)^8 + (512 : ℝ) * (b - a)^7 * (c - b)^1 + (1696 : ℝ) * (b - a)^6 * (c - b)^2 + (3296 : ℝ) * (b - a)^5 * (c - b)^3 + (3936 : ℝ) * (b - a)^4 * (c - b)^4 + (2976 : ℝ) * (b - a)^3 * (c - b)^5 + (1416 : ℝ) * (b - a)^2 * (c - b)^6 + (392 : ℝ) * (b - a)^1 * (c - b)^7 + (48 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (48*a^8 + 8*a^7*b + 8*a^7*c + 16*a^6*b^2 + 48*a^6*b*c + 16*a^6*c^2 + 24*a^5*b^3 - 88*a^5*b^2*c - 88*a^5*b*c^2 + 24*a^5*c^3 - 64*a^4*b^4 - 48*a^4*b^3*c + 224*a^4*b^2*c^2 - 48*a^4*b*c^3 - 64*a^4*c^4 + 24*a^3*b^5 - 48*a^3*b^4*c - 80*a^3*b^3*c^2 - 80*a^3*b^2*c^3 - 48*a^3*b*c^4 + 24*a^3*c^5 + 16*a^2*b^6 - 88*a^2*b^5*c + 224*a^2*b^4*c^2 - 80*a^2*b^3*c^3 + 224*a^2*b^2*c^4 - 88*a^2*b*c^5 + 16*a^2*c^6 + 8*a*b^7 + 48*a*b^6*c - 88*a*b^5*c^2 - 48*a*b^4*c^3 - 48*a*b^3*c^4 - 88*a*b^2*c^5 + 48*a*b*c^6 + 8*a*c^7 + 48*b^8 + 8*b^7*c + 16*b^6*c^2 + 24*b^5*c^3 - 64*b^4*c^4 + 24*b^3*c^5 + 16*b^2*c^6 + 8*b*c^7 + 48*c^8) := by
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
  have hn : 0 ≤ (48*a^8 + 8*a^7*b + 8*a^7*c + 16*a^6*b^2 + 48*a^6*b*c + 16*a^6*c^2 + 24*a^5*b^3 - 88*a^5*b^2*c - 88*a^5*b*c^2 + 24*a^5*c^3 - 64*a^4*b^4 - 48*a^4*b^3*c + 224*a^4*b^2*c^2 - 48*a^4*b*c^3 - 64*a^4*c^4 + 24*a^3*b^5 - 48*a^3*b^4*c - 80*a^3*b^3*c^2 - 80*a^3*b^2*c^3 - 48*a^3*b*c^4 + 24*a^3*c^5 + 16*a^2*b^6 - 88*a^2*b^5*c + 224*a^2*b^4*c^2 - 80*a^2*b^3*c^3 + 224*a^2*b^2*c^4 - 88*a^2*b*c^5 + 16*a^2*c^6 + 8*a*b^7 + 48*a*b^6*c - 88*a*b^5*c^2 - 48*a*b^4*c^3 - 48*a*b^3*c^4 - 88*a*b^2*c^5 + 48*a*b*c^6 + 8*a*c^7 + 48*b^8 + 8*b^7*c + 16*b^6*c^2 + 24*b^5*c^3 - 64*b^4*c^4 + 24*b^3*c^5 + 16*b^2*c^6 + 8*b*c^7 + 48*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b - c) ^ 2 / ((a + b) ^ 2 + c ^ 2) + (b + c - a) ^ 2 / ((b + c) ^ 2 + a ^ 2) + (c + a - b) ^ 2 / ((c + a) ^ 2 + b ^ 2) + 12 / 25 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 27 / 25) := @solution
#print axioms solution
