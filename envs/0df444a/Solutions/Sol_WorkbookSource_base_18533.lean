-- Prove2me | solution 1 for WorkbookSource.base_18533
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:37:17.395407+00:00
-- url     : https://prove2.me/submissions/814d5a19-43b1-429f-9d3d-389a2b523f5d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 / (9 * a + (b + 2 * c)^2) + b^2 / (9 * b + (c + 2 * a)^2) + c^2 / (9 * c + (a + 2 * b)^2)) ≥ 1 / 6  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (12*a^6 + 45*a^5*b + 36*a^5*c + 50*a^4*b^2 - a^4*b*c + 83*a^4*c^2 + 50*a^3*b^3 - 95*a^3*b^2*c - 107*a^3*b*c^2 + 50*a^3*c^3 + 83*a^2*b^4 - 107*a^2*b^3*c - 219*a^2*b^2*c^2 - 95*a^2*b*c^3 + 50*a^2*c^4 + 36*a*b^5 - a*b^4*c - 95*a*b^3*c^2 - 107*a*b^2*c^3 - a*b*c^4 + 45*a*c^5 + 12*b^6 + 45*b^5*c + 50*b^4*c^2 + 50*b^3*c^3 + 83*b^2*c^4 + 36*b*c^5 + 12*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1188 : ℝ) * a^4 * (b - a)^2 + (1188 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1188 : ℝ) * a^4 * (c - b)^2 + (3276 : ℝ) * a^3 * (b - a)^3 + (4995 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (4671 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (1476 : ℝ) * a^3 * (c - b)^3 + (3417 : ℝ) * a^2 * (b - a)^4 + (6996 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (7308 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (3729 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (717 : ℝ) * a^2 * (c - b)^4 + (1605 : ℝ) * a^1 * (b - a)^5 + (4104 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (4980 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (3285 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (1110 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (153 : ℝ) * a^1 * (c - b)^5 + (288 : ℝ) * (b - a)^6 + (879 : ℝ) * (b - a)^5 * (c - b)^1 + (1238 : ℝ) * (b - a)^4 * (c - b)^2 + (982 : ℝ) * (b - a)^3 * (c - b)^3 + (443 : ℝ) * (b - a)^2 * (c - b)^4 + (108 : ℝ) * (b - a)^1 * (c - b)^5 + (12 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (12*a^6 + 45*a^5*b + 36*a^5*c + 50*a^4*b^2 - a^4*b*c + 83*a^4*c^2 + 50*a^3*b^3 - 95*a^3*b^2*c - 107*a^3*b*c^2 + 50*a^3*c^3 + 83*a^2*b^4 - 107*a^2*b^3*c - 219*a^2*b^2*c^2 - 95*a^2*b*c^3 + 50*a^2*c^4 + 36*a*b^5 - a*b^4*c - 95*a*b^3*c^2 - 107*a*b^2*c^3 - a*b*c^4 + 45*a*c^5 + 12*b^6 + 45*b^5*c + 50*b^4*c^2 + 50*b^3*c^3 + 83*b^2*c^4 + 36*b*c^5 + 12*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1188 : ℝ) * a^4 * (c - a)^2 + (1188 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (1188 : ℝ) * a^4 * (b - c)^2 + (3276 : ℝ) * a^3 * (c - a)^3 + (4833 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (4509 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (1476 : ℝ) * a^3 * (b - c)^3 + (3417 : ℝ) * a^2 * (c - a)^4 + (6672 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (6822 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (3567 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (717 : ℝ) * a^2 * (b - c)^4 + (1605 : ℝ) * a^1 * (c - a)^5 + (3921 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (4614 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (3081 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1089 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (153 : ℝ) * a^1 * (b - c)^5 + (288 : ℝ) * (c - a)^6 + (849 : ℝ) * (c - a)^5 * (b - c)^1 + (1163 : ℝ) * (c - a)^4 * (b - c)^2 + (940 : ℝ) * (c - a)^3 * (b - c)^3 + (455 : ℝ) * (c - a)^2 * (b - c)^4 + (117 : ℝ) * (c - a)^1 * (b - c)^5 + (12 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (12*a^6 + 45*a^5*b + 36*a^5*c + 50*a^4*b^2 - a^4*b*c + 83*a^4*c^2 + 50*a^3*b^3 - 95*a^3*b^2*c - 107*a^3*b*c^2 + 50*a^3*c^3 + 83*a^2*b^4 - 107*a^2*b^3*c - 219*a^2*b^2*c^2 - 95*a^2*b*c^3 + 50*a^2*c^4 + 36*a*b^5 - a*b^4*c - 95*a*b^3*c^2 - 107*a*b^2*c^3 - a*b*c^4 + 45*a*c^5 + 12*b^6 + 45*b^5*c + 50*b^4*c^2 + 50*b^3*c^3 + 83*b^2*c^4 + 36*b*c^5 + 12*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (24*a^6 + 96*a^5*b + 24*a^5*c - 36*a^5 + 92*a^4*b^2 + 80*a^4*b*c - 90*a^4*b - 10*a^4*c^2 + 180*a^4*c - 16*a^3*b^3 + 28*a^3*b^2*c + 126*a^3*b^2 - 56*a^3*b*c^2 - 144*a^3*b*c - 81*a^3*b - 16*a^3*c^3 + 423*a^3*c^2 - 324*a^3*c - 10*a^2*b^4 - 56*a^2*b^3*c + 423*a^2*b^3 - 57*a^2*b^2*c^2 - 216*a^2*b^2*c - 324*a^2*b^2 + 28*a^2*b*c^3 - 216*a^2*b*c^2 + 486*a^2*b*c + 92*a^2*c^4 + 126*a^2*c^3 - 324*a^2*c^2 + 24*a*b^5 + 80*a*b^4*c + 180*a*b^4 + 28*a*b^3*c^2 - 144*a*b^3*c - 324*a*b^3 - 56*a*b^2*c^3 - 216*a*b^2*c^2 + 486*a*b^2*c + 80*a*b*c^4 - 144*a*b*c^3 + 486*a*b*c^2 - 729*a*b*c + 96*a*c^5 - 90*a*c^4 - 81*a*c^3 + 24*b^6 + 96*b^5*c - 36*b^5 + 92*b^4*c^2 - 90*b^4*c - 16*b^3*c^3 + 126*b^3*c^2 - 81*b^3*c - 10*b^2*c^4 + 423*b^2*c^3 - 324*b^2*c^2 + 24*b*c^5 + 180*b*c^4 - 324*b*c^3 + 24*c^6 - 36*c^5) = (12*a^6 + 45*a^5*b + 36*a^5*c + 50*a^4*b^2 - a^4*b*c + 83*a^4*c^2 + 50*a^3*b^3 - 95*a^3*b^2*c - 107*a^3*b*c^2 + 50*a^3*c^3 + 83*a^2*b^4 - 107*a^2*b^3*c - 219*a^2*b^2*c^2 - 95*a^2*b*c^3 + 50*a^2*c^4 + 36*a*b^5 - a*b^4*c - 95*a*b^3*c^2 - 107*a*b^2*c^3 - a*b*c^4 + 45*a*c^5 + 12*b^6 + 45*b^5*c + 50*b^4*c^2 + 50*b^3*c^3 + 83*b^2*c^4 + 36*b*c^5 + 12*c^6) := by
    linear_combination (12*a^5 + 39*a^4*b - 24*a^4*c + 3*a^3*b^2 + 66*a^3*b*c + 27*a^3*b - 69*a^3*c^2 + 108*a^3*c - 69*a^2*b^3 + 54*a^2*b^2*c + 108*a^2*b^2 + 54*a^2*b*c^2 - 81*a^2*b*c + 3*a^2*c^3 + 108*a^2*c^2 - 24*a*b^4 + 66*a*b^3*c + 108*a*b^3 + 54*a*b^2*c^2 - 81*a*b^2*c + 66*a*b*c^3 - 81*a*b*c^2 + 243*a*b*c + 39*a*c^4 + 27*a*c^3 + 12*b^5 + 39*b^4*c + 3*b^3*c^2 + 27*b^3*c - 69*b^2*c^3 + 108*b^2*c^2 - 24*b*c^4 + 108*b*c^3 + 12*c^5) * habc
  have hn : 0 ≤ (24*a^6 + 96*a^5*b + 24*a^5*c - 36*a^5 + 92*a^4*b^2 + 80*a^4*b*c - 90*a^4*b - 10*a^4*c^2 + 180*a^4*c - 16*a^3*b^3 + 28*a^3*b^2*c + 126*a^3*b^2 - 56*a^3*b*c^2 - 144*a^3*b*c - 81*a^3*b - 16*a^3*c^3 + 423*a^3*c^2 - 324*a^3*c - 10*a^2*b^4 - 56*a^2*b^3*c + 423*a^2*b^3 - 57*a^2*b^2*c^2 - 216*a^2*b^2*c - 324*a^2*b^2 + 28*a^2*b*c^3 - 216*a^2*b*c^2 + 486*a^2*b*c + 92*a^2*c^4 + 126*a^2*c^3 - 324*a^2*c^2 + 24*a*b^5 + 80*a*b^4*c + 180*a*b^4 + 28*a*b^3*c^2 - 144*a*b^3*c - 324*a*b^3 - 56*a*b^2*c^3 - 216*a*b^2*c^2 + 486*a*b^2*c + 80*a*b*c^4 - 144*a*b*c^3 + 486*a*b*c^2 - 729*a*b*c + 96*a*c^5 - 90*a*c^4 - 81*a*c^3 + 24*b^6 + 96*b^5*c - 36*b^5 + 92*b^4*c^2 - 90*b^4*c - 16*b^3*c^3 + 126*b^3*c^2 - 81*b^3*c - 10*b^2*c^4 + 423*b^2*c^3 - 324*b^2*c^2 + 24*b*c^5 + 180*b*c^4 - 324*b*c^3 + 24*c^6 - 36*c^5) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^2 / (9 * a + (b + 2 * c)^2) + b^2 / (9 * b + (c + 2 * a)^2) + c^2 / (9 * c + (a + 2 * b)^2)) ≥ 1 / 6) := @solution
#print axioms solution
