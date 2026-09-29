-- Prove2me | solution 1 for WorkbookSource.base_32573
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:44:52.245926+00:00
-- url     : https://prove2.me/submissions/904bc0bf-9cbc-42bf-b291-0ad049a57edf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (5 * c ^ 2 + a * b) + (b + c) / (5 * a ^ 2 + b * c) + (c + a) / (5 * b ^ 2 + c * a) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / (3 * a * b * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^6*b*c + 25*a^5*b^3 - 15*a^5*b^2*c - 15*a^5*b*c^2 + 25*a^5*c^3 - 70*a^4*b^3*c + 96*a^4*b^2*c^2 - 70*a^4*b*c^3 + 25*a^3*b^5 - 70*a^3*b^4*c + 19*a^3*b^3*c^2 + 19*a^3*b^2*c^3 - 70*a^3*b*c^4 + 25*a^3*c^5 - 15*a^2*b^5*c + 96*a^2*b^4*c^2 + 19*a^2*b^3*c^3 + 96*a^2*b^2*c^4 - 15*a^2*b*c^5 + 5*a*b^6*c - 15*a*b^5*c^2 - 70*a*b^4*c^3 - 70*a*b^3*c^4 - 15*a*b^2*c^5 + 5*a*b*c^6 + 25*b^5*c^3 + 25*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^6 * (b - a)^2 + (36 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^6 * (c - b)^2 + (144 : ℝ) * a^5 * (b - a)^3 + (216 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (216 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (72 : ℝ) * a^5 * (c - b)^3 + (311 : ℝ) * a^4 * (b - a)^4 + (622 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (753 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (442 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (131 : ℝ) * a^4 * (c - b)^4 + (474 : ℝ) * a^3 * (b - a)^5 + (1185 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1522 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1098 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (387 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (50 : ℝ) * a^3 * (c - b)^5 + (461 : ℝ) * a^2 * (b - a)^6 + (1383 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1854 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1403 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (561 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (90 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (5 : ℝ) * a^2 * (c - b)^6 + (240 : ℝ) * a^1 * (b - a)^7 + (840 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (1230 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (975 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (430 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (90 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (5 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (50 : ℝ) * (b - a)^8 + (200 : ℝ) * (b - a)^7 * (c - b)^1 + (325 : ℝ) * (b - a)^6 * (c - b)^2 + (275 : ℝ) * (b - a)^5 * (c - b)^3 + (125 : ℝ) * (b - a)^4 * (c - b)^4 + (25 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^6*b*c + 25*a^5*b^3 - 15*a^5*b^2*c - 15*a^5*b*c^2 + 25*a^5*c^3 - 70*a^4*b^3*c + 96*a^4*b^2*c^2 - 70*a^4*b*c^3 + 25*a^3*b^5 - 70*a^3*b^4*c + 19*a^3*b^3*c^2 + 19*a^3*b^2*c^3 - 70*a^3*b*c^4 + 25*a^3*c^5 - 15*a^2*b^5*c + 96*a^2*b^4*c^2 + 19*a^2*b^3*c^3 + 96*a^2*b^2*c^4 - 15*a^2*b*c^5 + 5*a*b^6*c - 15*a*b^5*c^2 - 70*a*b^4*c^3 - 70*a*b^3*c^4 - 15*a*b^2*c^5 + 5*a*b*c^6 + 25*b^5*c^3 + 25*b^3*c^5) := by
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
  have hn : 0 ≤ (5*a^6*b*c + 25*a^5*b^3 - 15*a^5*b^2*c - 15*a^5*b*c^2 + 25*a^5*c^3 - 70*a^4*b^3*c + 96*a^4*b^2*c^2 - 70*a^4*b*c^3 + 25*a^3*b^5 - 70*a^3*b^4*c + 19*a^3*b^3*c^2 + 19*a^3*b^2*c^3 - 70*a^3*b*c^4 + 25*a^3*c^5 - 15*a^2*b^5*c + 96*a^2*b^4*c^2 + 19*a^2*b^3*c^3 + 96*a^2*b^2*c^4 - 15*a^2*b*c^5 + 5*a*b^6*c - 15*a*b^5*c^2 - 70*a*b^4*c^3 - 70*a*b^3*c^4 - 15*a*b^2*c^5 + 5*a*b*c^6 + 25*b^5*c^3 + 25*b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (5 * c ^ 2 + a * b) + (b + c) / (5 * a ^ 2 + b * c) + (c + a) / (5 * b ^ 2 + c * a) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / (3 * a * b * c)) := @solution
#print axioms solution
