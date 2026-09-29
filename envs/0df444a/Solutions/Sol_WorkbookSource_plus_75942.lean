-- Prove2me | solution 1 for WorkbookSource.plus_75942
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:46:39.316101+00:00
-- url     : https://prove2.me/submissions/83f43b68-70bf-4335-ba1d-a7c44cf8ee3e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (b + c) * (c + a) * ((a + b + c) ^ 2 + a * b + b * c + c * a) ^ 2 ≥ 32 * a * b * c * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) ^ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b + a^6*c + 7*a^5*b^2 - 18*a^5*b*c + 7*a^5*c^2 + 17*a^4*b^3 - 10*a^4*b^2*c - 10*a^4*b*c^2 + 17*a^4*c^3 + 17*a^3*b^4 - 14*a^3*b^3*c + 2*a^3*b^2*c^2 - 14*a^3*b*c^3 + 17*a^3*c^4 + 7*a^2*b^5 - 10*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - 10*a^2*b*c^4 + 7*a^2*c^5 + a*b^6 - 18*a*b^5*c - 10*a*b^4*c^2 - 14*a*b^3*c^3 - 10*a*b^2*c^4 - 18*a*b*c^5 + a*c^6 + b^6*c + 7*b^5*c^2 + 17*b^4*c^3 + 17*b^3*c^4 + 7*b^2*c^5 + b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^5 * (b - a)^2 + (96 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^5 * (c - b)^2 + (416 : ℝ) * a^4 * (b - a)^3 + (624 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (336 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (64 : ℝ) * a^4 * (c - b)^3 + (728 : ℝ) * a^3 * (b - a)^4 + (1456 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (904 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (176 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (24 : ℝ) * a^3 * (c - b)^4 + (640 : ℝ) * a^2 * (b - a)^5 + (1600 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (1360 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (440 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (56 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (8 : ℝ) * a^2 * (c - b)^5 + (282 : ℝ) * a^1 * (b - a)^6 + (846 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (948 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (486 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (116 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (14 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^1 * (c - b)^6 + (50 : ℝ) * (b - a)^7 + (175 : ℝ) * (b - a)^6 * (c - b)^1 + (245 : ℝ) * (b - a)^5 * (c - b)^2 + (175 : ℝ) * (b - a)^4 * (c - b)^3 + (67 : ℝ) * (b - a)^3 * (c - b)^4 + (13 : ℝ) * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b + a^6*c + 7*a^5*b^2 - 18*a^5*b*c + 7*a^5*c^2 + 17*a^4*b^3 - 10*a^4*b^2*c - 10*a^4*b*c^2 + 17*a^4*c^3 + 17*a^3*b^4 - 14*a^3*b^3*c + 2*a^3*b^2*c^2 - 14*a^3*b*c^3 + 17*a^3*c^4 + 7*a^2*b^5 - 10*a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - 10*a^2*b*c^4 + 7*a^2*c^5 + a*b^6 - 18*a*b^5*c - 10*a*b^4*c^2 - 14*a*b^3*c^3 - 10*a*b^2*c^4 - 18*a*b*c^5 + a*c^6 + b^6*c + 7*b^5*c^2 + 17*b^4*c^3 + 17*b^3*c^4 + 7*b^2*c^5 + b*c^6) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) * (b + c) * (c + a) * ((a + b + c) ^ 2 + a * b + b * c + c * a) ^ 2 ≥ 32 * a * b * c * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) ^ 2) := @solution
#print axioms solution
