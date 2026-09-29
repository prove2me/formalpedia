-- Prove2me | solution 1 for WorkbookSource.base_9655
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:44:19.657654+00:00
-- url     : https://prove2.me/submissions/b8ef64e1-2c1e-43a8-9e3a-ab7bf12f2556

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (1 / a + 1 / (b + c) + 1 / (a + b + c)) + b / (1 / b + 1 / (c + a) + 1 / (a + b + c)) + c / (1 / c + 1 / (a + b) + 1 / (a + b + c)) ≤ 6 / 11 * (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^8 + 37*a^7*b + 37*a^7*c + 73*a^6*b^2 + 174*a^6*b*c + 73*a^6*c^2 + 43*a^5*b^3 + 194*a^5*b^2*c + 194*a^5*b*c^2 + 43*a^5*c^3 + 2*a^4*b^4 - 65*a^4*b^3*c - 164*a^4*b^2*c^2 - 65*a^4*b*c^3 + 2*a^4*c^4 + 43*a^3*b^5 - 65*a^3*b^4*c - 582*a^3*b^3*c^2 - 582*a^3*b^2*c^3 - 65*a^3*b*c^4 + 43*a^3*c^5 + 73*a^2*b^6 + 194*a^2*b^5*c - 164*a^2*b^4*c^2 - 582*a^2*b^3*c^3 - 164*a^2*b^2*c^4 + 194*a^2*b*c^5 + 73*a^2*c^6 + 37*a*b^7 + 174*a*b^6*c + 194*a*b^5*c^2 - 65*a*b^4*c^3 - 65*a*b^3*c^4 + 194*a*b^2*c^5 + 174*a*b*c^6 + 37*a*c^7 + 6*b^8 + 37*b^7*c + 73*b^6*c^2 + 43*b^5*c^3 + 2*b^4*c^4 + 43*b^3*c^5 + 73*b^2*c^6 + 37*b*c^7 + 6*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5522 : ℝ) * a^6 * (b - a)^2 + (5522 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (5522 : ℝ) * a^6 * (c - b)^2 + (21434 : ℝ) * a^5 * (b - a)^3 + (32151 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (34113 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (11698 : ℝ) * a^5 * (c - b)^3 + (34230 : ℝ) * a^4 * (b - a)^4 + (68460 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (83255 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (49025 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (9890 : ℝ) * a^4 * (c - b)^4 + (28736 : ℝ) * a^3 * (b - a)^5 + (71840 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (101316 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (80134 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (30490 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (4284 : ℝ) * a^3 * (c - b)^5 + (13344 : ℝ) * a^2 * (b - a)^6 + (40032 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (65081 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (63442 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (34493 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (9444 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1006 : ℝ) * a^2 * (c - b)^6 + (3240 : ℝ) * a^1 * (b - a)^7 + (11340 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (21040 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (24250 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (16918 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (6797 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (1433 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (122 : ℝ) * a^1 * (c - b)^7 + (320 : ℝ) * (b - a)^8 + (1280 : ℝ) * (b - a)^7 * (c - b)^1 + (2684 : ℝ) * (b - a)^6 * (c - b)^2 + (3572 : ℝ) * (b - a)^5 * (c - b)^3 + (3027 : ℝ) * (b - a)^4 * (c - b)^4 + (1594 : ℝ) * (b - a)^3 * (c - b)^5 + (500 : ℝ) * (b - a)^2 * (c - b)^6 + (85 : ℝ) * (b - a)^1 * (c - b)^7 + (6 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^8 + 37*a^7*b + 37*a^7*c + 73*a^6*b^2 + 174*a^6*b*c + 73*a^6*c^2 + 43*a^5*b^3 + 194*a^5*b^2*c + 194*a^5*b*c^2 + 43*a^5*c^3 + 2*a^4*b^4 - 65*a^4*b^3*c - 164*a^4*b^2*c^2 - 65*a^4*b*c^3 + 2*a^4*c^4 + 43*a^3*b^5 - 65*a^3*b^4*c - 582*a^3*b^3*c^2 - 582*a^3*b^2*c^3 - 65*a^3*b*c^4 + 43*a^3*c^5 + 73*a^2*b^6 + 194*a^2*b^5*c - 164*a^2*b^4*c^2 - 582*a^2*b^3*c^3 - 164*a^2*b^2*c^4 + 194*a^2*b*c^5 + 73*a^2*c^6 + 37*a*b^7 + 174*a*b^6*c + 194*a*b^5*c^2 - 65*a*b^4*c^3 - 65*a*b^3*c^4 + 194*a*b^2*c^5 + 174*a*b*c^6 + 37*a*c^7 + 6*b^8 + 37*b^7*c + 73*b^6*c^2 + 43*b^5*c^3 + 2*b^4*c^4 + 43*b^3*c^5 + 73*b^2*c^6 + 37*b*c^7 + 6*c^8) := by
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
  have hn : 0 ≤ (6*a^8 + 37*a^7*b + 37*a^7*c + 73*a^6*b^2 + 174*a^6*b*c + 73*a^6*c^2 + 43*a^5*b^3 + 194*a^5*b^2*c + 194*a^5*b*c^2 + 43*a^5*c^3 + 2*a^4*b^4 - 65*a^4*b^3*c - 164*a^4*b^2*c^2 - 65*a^4*b*c^3 + 2*a^4*c^4 + 43*a^3*b^5 - 65*a^3*b^4*c - 582*a^3*b^3*c^2 - 582*a^3*b^2*c^3 - 65*a^3*b*c^4 + 43*a^3*c^5 + 73*a^2*b^6 + 194*a^2*b^5*c - 164*a^2*b^4*c^2 - 582*a^2*b^3*c^3 - 164*a^2*b^2*c^4 + 194*a^2*b*c^5 + 73*a^2*c^6 + 37*a*b^7 + 174*a*b^6*c + 194*a*b^5*c^2 - 65*a*b^4*c^3 - 65*a*b^3*c^4 + 194*a*b^2*c^5 + 174*a*b*c^6 + 37*a*c^7 + 6*b^8 + 37*b^7*c + 73*b^6*c^2 + 43*b^5*c^3 + 2*b^4*c^4 + 43*b^3*c^5 + 73*b^2*c^6 + 37*b*c^7 + 6*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a / (1 / a + 1 / (b + c) + 1 / (a + b + c)) + b / (1 / b + 1 / (c + a) + 1 / (a + b + c)) + c / (1 / c + 1 / (a + b) + 1 / (a + b + c)) ≤ 6 / 11 * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
