-- Prove2me | solution 1 for WorkbookSource.base_4320
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:12.820555+00:00
-- url     : https://prove2.me/submissions/118a01b8-293d-491a-a936-178b2c1017bc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 - 3*c^2) / (a^2 + a*b + b^2) + (b^2 + c^2 - 3*a^2) / (b^2 + b*c + c^2) + (c^2 + a^2 - 3*b^2) / (c^2 + c*a + a^2) + (4 * (a*b + b*c + a*c)) / (3 * (a^2 + b^2 + c^2)) ≤ 1 / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (9*a^8 + 9*a^7*b + 9*a^7*c + 10*a^6*b^2 + 4*a^6*b*c + 10*a^6*c^2 + 3*a^5*b^2*c + 3*a^5*b*c^2 - 2*a^4*b^4 - 10*a^4*b^3*c - 6*a^4*b^2*c^2 - 10*a^4*b*c^3 - 2*a^4*c^4 - 10*a^3*b^4*c - 29*a^3*b^3*c^2 - 29*a^3*b^2*c^3 - 10*a^3*b*c^4 + 10*a^2*b^6 + 3*a^2*b^5*c - 6*a^2*b^4*c^2 - 29*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 3*a^2*b*c^5 + 10*a^2*c^6 + 9*a*b^7 + 4*a*b^6*c + 3*a*b^5*c^2 - 10*a*b^4*c^3 - 10*a*b^3*c^4 + 3*a*b^2*c^5 + 4*a*b*c^6 + 9*a*c^7 + 9*b^8 + 9*b^7*c + 10*b^6*c^2 - 2*b^4*c^4 + 10*b^2*c^6 + 9*b*c^7 + 9*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (621 : ℝ) * a^6 * (b - a)^2 + (621 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (621 : ℝ) * a^6 * (c - b)^2 + (2250 : ℝ) * a^5 * (b - a)^3 + (3375 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (4077 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (1476 : ℝ) * a^5 * (c - b)^3 + (3555 : ℝ) * a^4 * (b - a)^4 + (7110 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (10485 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (6930 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (1620 : ℝ) * a^4 * (c - b)^4 + (3108 : ℝ) * a^3 * (b - a)^5 + (7770 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (13728 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (12822 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (5820 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (1032 : ℝ) * a^3 * (c - b)^5 + (1581 : ℝ) * a^2 * (b - a)^6 + (4743 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (9846 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (11787 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (7857 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (2754 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (402 : ℝ) * a^2 * (c - b)^6 + (444 : ℝ) * a^1 * (b - a)^7 + (1554 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (3726 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (5430 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (4752 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (2475 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (717 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (90 : ℝ) * a^1 * (c - b)^7 + (54 : ℝ) * (b - a)^8 + (216 : ℝ) * (b - a)^7 * (c - b)^1 + (589 : ℝ) * (b - a)^6 * (c - b)^2 + (1011 : ℝ) * (b - a)^5 * (c - b)^3 + (1093 : ℝ) * (b - a)^4 * (c - b)^4 + (753 : ℝ) * (b - a)^3 * (c - b)^5 + (325 : ℝ) * (b - a)^2 * (c - b)^6 + (81 : ℝ) * (b - a)^1 * (c - b)^7 + (9 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (9*a^8 + 9*a^7*b + 9*a^7*c + 10*a^6*b^2 + 4*a^6*b*c + 10*a^6*c^2 + 3*a^5*b^2*c + 3*a^5*b*c^2 - 2*a^4*b^4 - 10*a^4*b^3*c - 6*a^4*b^2*c^2 - 10*a^4*b*c^3 - 2*a^4*c^4 - 10*a^3*b^4*c - 29*a^3*b^3*c^2 - 29*a^3*b^2*c^3 - 10*a^3*b*c^4 + 10*a^2*b^6 + 3*a^2*b^5*c - 6*a^2*b^4*c^2 - 29*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 3*a^2*b*c^5 + 10*a^2*c^6 + 9*a*b^7 + 4*a*b^6*c + 3*a*b^5*c^2 - 10*a*b^4*c^3 - 10*a*b^3*c^4 + 3*a*b^2*c^5 + 4*a*b*c^6 + 9*a*c^7 + 9*b^8 + 9*b^7*c + 10*b^6*c^2 - 2*b^4*c^4 + 10*b^2*c^6 + 9*b*c^7 + 9*c^8) := by
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
  have hn : 0 ≤ (9*a^8 + 9*a^7*b + 9*a^7*c + 10*a^6*b^2 + 4*a^6*b*c + 10*a^6*c^2 + 3*a^5*b^2*c + 3*a^5*b*c^2 - 2*a^4*b^4 - 10*a^4*b^3*c - 6*a^4*b^2*c^2 - 10*a^4*b*c^3 - 2*a^4*c^4 - 10*a^3*b^4*c - 29*a^3*b^3*c^2 - 29*a^3*b^2*c^3 - 10*a^3*b*c^4 + 10*a^2*b^6 + 3*a^2*b^5*c - 6*a^2*b^4*c^2 - 29*a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 3*a^2*b*c^5 + 10*a^2*c^6 + 9*a*b^7 + 4*a*b^6*c + 3*a*b^5*c^2 - 10*a*b^4*c^3 - 10*a*b^3*c^4 + 3*a*b^2*c^5 + 4*a*b*c^6 + 9*a*c^7 + 9*b^8 + 9*b^7*c + 10*b^6*c^2 - 2*b^4*c^4 + 10*b^2*c^6 + 9*b*c^7 + 9*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 - 3*c^2) / (a^2 + a*b + b^2) + (b^2 + c^2 - 3*a^2) / (b^2 + b*c + c^2) + (c^2 + a^2 - 3*b^2) / (c^2 + c*a + a^2) + (4 * (a*b + b*c + a*c)) / (3 * (a^2 + b^2 + c^2)) ≤ 1 / 3) := @solution
#print axioms solution
