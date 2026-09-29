-- Prove2me | solution 1 for WorkbookSource.plus_7717
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:17.975363+00:00
-- url     : https://prove2.me/submissions/6bbb8cda-5c69-4224-9f91-c987dd5788c1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c) / (b ^ 2 + c ^ 2) + b * (c + a) / (c ^ 2 + a ^ 2) + c * (a + b) / (a ^ 2 + b ^ 2) + 7 / 6 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c)) ≥ 25 / 6   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (13*a^6*b^2 + 12*a^6*b*c + 13*a^6*c^2 - 25*a^5*b^3 - 19*a^5*b^2*c - 19*a^5*b*c^2 - 25*a^5*c^3 + 26*a^4*b^4 - a^4*b^3*c + 52*a^4*b^2*c^2 - a^4*b*c^3 + 26*a^4*c^4 - 25*a^3*b^5 - a^3*b^4*c - 26*a^3*b^3*c^2 - 26*a^3*b^2*c^3 - a^3*b*c^4 - 25*a^3*c^5 + 13*a^2*b^6 - 19*a^2*b^5*c + 52*a^2*b^4*c^2 - 26*a^2*b^3*c^3 + 52*a^2*b^2*c^4 - 19*a^2*b*c^5 + 13*a^2*c^6 + 12*a*b^6*c - 19*a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 - 19*a*b^2*c^5 + 12*a*b*c^6 + 13*b^6*c^2 - 25*b^5*c^3 + 26*b^4*c^4 - 25*b^3*c^5 + 13*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (56 : ℝ) * a^6 * (b - a)^2 + (56 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (56 : ℝ) * a^6 * (c - b)^2 + (152 : ℝ) * a^5 * (b - a)^3 + (228 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (444 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (184 : ℝ) * a^5 * (c - b)^3 + (152 : ℝ) * a^4 * (b - a)^4 + (304 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1076 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (924 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (232 : ℝ) * a^4 * (c - b)^4 + (68 : ℝ) * a^3 * (b - a)^5 + (170 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1204 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1636 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (814 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (140 : ℝ) * a^3 * (c - b)^5 + (10 : ℝ) * a^2 * (b - a)^6 + (30 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (686 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1322 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (980 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (324 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (38 : ℝ) * a^2 * (c - b)^6 + (196 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (490 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (468 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (212 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (38 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2 : ℝ) * (b - a)^8 + (8 : ℝ) * (b - a)^7 * (c - b)^1 + (39 : ℝ) * (b - a)^6 * (c - b)^2 + (89 : ℝ) * (b - a)^5 * (c - b)^3 + (96 : ℝ) * (b - a)^4 * (c - b)^4 + (53 : ℝ) * (b - a)^3 * (c - b)^5 + (13 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (13*a^6*b^2 + 12*a^6*b*c + 13*a^6*c^2 - 25*a^5*b^3 - 19*a^5*b^2*c - 19*a^5*b*c^2 - 25*a^5*c^3 + 26*a^4*b^4 - a^4*b^3*c + 52*a^4*b^2*c^2 - a^4*b*c^3 + 26*a^4*c^4 - 25*a^3*b^5 - a^3*b^4*c - 26*a^3*b^3*c^2 - 26*a^3*b^2*c^3 - a^3*b*c^4 - 25*a^3*c^5 + 13*a^2*b^6 - 19*a^2*b^5*c + 52*a^2*b^4*c^2 - 26*a^2*b^3*c^3 + 52*a^2*b^2*c^4 - 19*a^2*b*c^5 + 13*a^2*c^6 + 12*a*b^6*c - 19*a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 - 19*a*b^2*c^5 + 12*a*b*c^6 + 13*b^6*c^2 - 25*b^5*c^3 + 26*b^4*c^4 - 25*b^3*c^5 + 13*b^2*c^6) := by
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
  have hn : 0 ≤ (13*a^6*b^2 + 12*a^6*b*c + 13*a^6*c^2 - 25*a^5*b^3 - 19*a^5*b^2*c - 19*a^5*b*c^2 - 25*a^5*c^3 + 26*a^4*b^4 - a^4*b^3*c + 52*a^4*b^2*c^2 - a^4*b*c^3 + 26*a^4*c^4 - 25*a^3*b^5 - a^3*b^4*c - 26*a^3*b^3*c^2 - 26*a^3*b^2*c^3 - a^3*b*c^4 - 25*a^3*c^5 + 13*a^2*b^6 - 19*a^2*b^5*c + 52*a^2*b^4*c^2 - 26*a^2*b^3*c^3 + 52*a^2*b^2*c^4 - 19*a^2*b*c^5 + 13*a^2*c^6 + 12*a*b^6*c - 19*a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 - 19*a*b^2*c^5 + 12*a*b*c^6 + 13*b^6*c^2 - 25*b^5*c^3 + 26*b^4*c^4 - 25*b^3*c^5 + 13*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (b + c) / (b ^ 2 + c ^ 2) + b * (c + a) / (c ^ 2 + a ^ 2) + c * (a + b) / (a ^ 2 + b ^ 2) + 7 / 6 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c)) ≥ 25 / 6) := @solution
#print axioms solution
