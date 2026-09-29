-- Prove2me | solution 1 for WorkbookSource.base_29386
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:14:19.367879+00:00
-- url     : https://prove2.me/submissions/3752ceff-0e77-4f1d-bccc-b3ff2a851183

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a / (4 * a ^ 2 + b ^ 2 + (b + c) ^ 2) + b / (4 * b ^ 2 + c ^ 2 + (c + a) ^ 2) + c / (4 * c ^ 2 + a ^ 2 + (a + b) ^ 2)) ≤ 1 / (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^6 - 4*a^5*b + 6*a^5*c + 13*a^4*b^2 - 2*a^4*b*c + 10*a^4*c^2 + 3*a^3*b^3 - 25*a^3*b^2*c - 18*a^3*b*c^2 + 3*a^3*c^3 + 10*a^2*b^4 - 18*a^2*b^3*c + 33*a^2*b^2*c^2 - 25*a^2*b*c^3 + 13*a^2*c^4 + 6*a*b^5 - 2*a*b^4*c - 25*a*b^3*c^2 - 18*a*b^2*c^3 - 2*a*b*c^4 - 4*a*c^5 + 6*b^6 - 4*b^5*c + 13*b^4*c^2 + 3*b^3*c^3 + 10*b^2*c^4 + 6*b*c^5 + 6*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (138 : ℝ) * a^4 * (b - a)^2 + (138 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (138 : ℝ) * a^4 * (c - b)^2 + (365 : ℝ) * a^3 * (b - a)^3 + (589 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (598 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (187 : ℝ) * a^3 * (c - b)^3 + (388 : ℝ) * a^2 * (b - a)^4 + (859 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1035 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (564 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (121 : ℝ) * a^2 * (c - b)^4 + (195 : ℝ) * a^1 * (b - a)^5 + (551 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (797 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (603 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (238 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (38 : ℝ) * a^1 * (c - b)^5 + (40 : ℝ) * (b - a)^6 + (137 : ℝ) * (b - a)^5 * (c - b)^1 + (232 : ℝ) * (b - a)^4 * (c - b)^2 + (223 : ℝ) * (b - a)^3 * (c - b)^3 + (130 : ℝ) * (b - a)^2 * (c - b)^4 + (42 : ℝ) * (b - a)^1 * (c - b)^5 + (6 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (6*a^6 - 4*a^5*b + 6*a^5*c + 13*a^4*b^2 - 2*a^4*b*c + 10*a^4*c^2 + 3*a^3*b^3 - 25*a^3*b^2*c - 18*a^3*b*c^2 + 3*a^3*c^3 + 10*a^2*b^4 - 18*a^2*b^3*c + 33*a^2*b^2*c^2 - 25*a^2*b*c^3 + 13*a^2*c^4 + 6*a*b^5 - 2*a*b^4*c - 25*a*b^3*c^2 - 18*a*b^2*c^3 - 2*a*b*c^4 - 4*a*c^5 + 6*b^6 - 4*b^5*c + 13*b^4*c^2 + 3*b^3*c^3 + 10*b^2*c^4 + 6*b*c^5 + 6*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (138 : ℝ) * a^4 * (c - a)^2 + (138 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (138 : ℝ) * a^4 * (b - c)^2 + (365 : ℝ) * a^3 * (c - a)^3 + (506 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (515 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (187 : ℝ) * a^3 * (b - c)^3 + (388 : ℝ) * a^2 * (c - a)^4 + (693 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (786 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (481 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (121 : ℝ) * a^2 * (b - c)^4 + (195 : ℝ) * a^1 * (c - a)^5 + (424 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (543 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (432 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (194 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (38 : ℝ) * a^1 * (b - c)^5 + (40 : ℝ) * (c - a)^6 + (103 : ℝ) * (c - a)^5 * (b - c)^1 + (147 : ℝ) * (c - a)^4 * (b - c)^2 + (135 : ℝ) * (c - a)^3 * (b - c)^3 + (83 : ℝ) * (c - a)^2 * (b - c)^4 + (32 : ℝ) * (c - a)^1 * (b - c)^5 + (6 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^6 - 4*a^5*b + 6*a^5*c + 13*a^4*b^2 - 2*a^4*b*c + 10*a^4*c^2 + 3*a^3*b^3 - 25*a^3*b^2*c - 18*a^3*b*c^2 + 3*a^3*c^3 + 10*a^2*b^4 - 18*a^2*b^3*c + 33*a^2*b^2*c^2 - 25*a^2*b*c^3 + 13*a^2*c^4 + 6*a*b^5 - 2*a*b^4*c - 25*a*b^3*c^2 - 18*a*b^2*c^3 - 2*a*b*c^4 - 4*a*c^5 + 6*b^6 - 4*b^5*c + 13*b^4*c^2 + 3*b^3*c^3 + 10*b^2*c^4 + 6*b*c^5 + 6*c^6) := by
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
  have hn : 0 ≤ (6*a^6 - 4*a^5*b + 6*a^5*c + 13*a^4*b^2 - 2*a^4*b*c + 10*a^4*c^2 + 3*a^3*b^3 - 25*a^3*b^2*c - 18*a^3*b*c^2 + 3*a^3*c^3 + 10*a^2*b^4 - 18*a^2*b^3*c + 33*a^2*b^2*c^2 - 25*a^2*b*c^3 + 13*a^2*c^4 + 6*a*b^5 - 2*a*b^4*c - 25*a*b^3*c^2 - 18*a*b^2*c^3 - 2*a*b*c^4 - 4*a*c^5 + 6*b^6 - 4*b^5*c + 13*b^4*c^2 + 3*b^3*c^3 + 10*b^2*c^4 + 6*b*c^5 + 6*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (a / (4 * a ^ 2 + b ^ 2 + (b + c) ^ 2) + b / (4 * b ^ 2 + c ^ 2 + (c + a) ^ 2) + c / (4 * c ^ 2 + a ^ 2 + (a + b) ^ 2)) ≤ 1 / (a + b + c)) := @solution
#print axioms solution
