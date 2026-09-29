-- Prove2me | solution 1 for WorkbookSource.plus_62807
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:41:34.120042+00:00
-- url     : https://prove2.me/submissions/5191601c-1ef3-45ce-8a5f-9fd1201da866

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (2 * c ^ 2 + a * b + b * c) + b * c / (2 * a ^ 2 + b * c + c * a) + c * a / (2 * b ^ 2 + c * a + a * b)) ≤ (3 / 4) * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^6*b^2 + 6*a^6*b*c + 4*a^5*b^3 - 15*a^5*b^2*c + 5*a^5*b*c^2 + 12*a^5*c^3 - 10*a^4*b^4 - a^4*b^3*c - 17*a^4*b*c^3 - 10*a^4*c^4 + 12*a^3*b^5 - 17*a^3*b^4*c + 10*a^3*b^3*c^2 + 10*a^3*b^2*c^3 - a^3*b*c^4 + 4*a^3*c^5 + 5*a^2*b^5*c + 10*a^2*b^3*c^3 - 15*a^2*b*c^5 + 6*a^2*c^6 + 6*a*b^6*c - 15*a*b^5*c^2 - a*b^4*c^3 - 17*a*b^3*c^4 + 5*a*b^2*c^5 + 6*a*b*c^6 + 6*b^6*c^2 + 4*b^5*c^3 - 10*b^4*c^4 + 12*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^6 * (b - a)^2 + (72 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (72 : ℝ) * a^6 * (c - b)^2 + (266 : ℝ) * a^5 * (b - a)^3 + (423 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (489 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (166 : ℝ) * a^5 * (c - b)^3 + (422 : ℝ) * a^4 * (b - a)^4 + (924 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1301 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (799 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (172 : ℝ) * a^4 * (c - b)^4 + (390 : ℝ) * a^3 * (b - a)^5 + (1059 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1714 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1432 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (543 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (78 : ℝ) * a^3 * (c - b)^5 + (230 : ℝ) * a^2 * (b - a)^6 + (716 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1240 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1224 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (609 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (139 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (12 : ℝ) * a^2 * (c - b)^6 + (80 : ℝ) * a^1 * (b - a)^7 + (274 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (488 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (521 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (298 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (77 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (12 : ℝ) * (b - a)^8 + (44 : ℝ) * (b - a)^7 * (c - b)^1 + (78 : ℝ) * (b - a)^6 * (c - b)^2 + (84 : ℝ) * (b - a)^5 * (c - b)^3 + (50 : ℝ) * (b - a)^4 * (c - b)^4 + (12 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (6*a^6*b^2 + 6*a^6*b*c + 4*a^5*b^3 - 15*a^5*b^2*c + 5*a^5*b*c^2 + 12*a^5*c^3 - 10*a^4*b^4 - a^4*b^3*c - 17*a^4*b*c^3 - 10*a^4*c^4 + 12*a^3*b^5 - 17*a^3*b^4*c + 10*a^3*b^3*c^2 + 10*a^3*b^2*c^3 - a^3*b*c^4 + 4*a^3*c^5 + 5*a^2*b^5*c + 10*a^2*b^3*c^3 - 15*a^2*b*c^5 + 6*a^2*c^6 + 6*a*b^6*c - 15*a*b^5*c^2 - a*b^4*c^3 - 17*a*b^3*c^4 + 5*a*b^2*c^5 + 6*a*b*c^6 + 6*b^6*c^2 + 4*b^5*c^3 - 10*b^4*c^4 + 12*b^3*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^6 * (c - a)^2 + (72 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (72 : ℝ) * a^6 * (b - c)^2 + (266 : ℝ) * a^5 * (c - a)^3 + (375 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (441 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (166 : ℝ) * a^5 * (b - c)^3 + (422 : ℝ) * a^4 * (c - a)^4 + (764 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (1061 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (719 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (172 : ℝ) * a^4 * (b - c)^4 + (390 : ℝ) * a^3 * (c - a)^5 + (891 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (1378 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (1256 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (535 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (78 : ℝ) * a^3 * (b - c)^5 + (230 : ℝ) * a^2 * (c - a)^6 + (664 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (1110 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (1176 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (667 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (167 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (12 : ℝ) * a^2 * (b - c)^6 + (80 : ℝ) * a^1 * (c - a)^7 + (286 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (524 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (609 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (414 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (141 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (18 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (12 : ℝ) * (c - a)^8 + (52 : ℝ) * (c - a)^7 * (b - c)^1 + (106 : ℝ) * (c - a)^6 * (b - c)^2 + (132 : ℝ) * (c - a)^5 * (b - c)^3 + (100 : ℝ) * (c - a)^4 * (b - c)^4 + (40 : ℝ) * (c - a)^3 * (b - c)^5 + (6 : ℝ) * (c - a)^2 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^6*b^2 + 6*a^6*b*c + 4*a^5*b^3 - 15*a^5*b^2*c + 5*a^5*b*c^2 + 12*a^5*c^3 - 10*a^4*b^4 - a^4*b^3*c - 17*a^4*b*c^3 - 10*a^4*c^4 + 12*a^3*b^5 - 17*a^3*b^4*c + 10*a^3*b^3*c^2 + 10*a^3*b^2*c^3 - a^3*b*c^4 + 4*a^3*c^5 + 5*a^2*b^5*c + 10*a^2*b^3*c^3 - 15*a^2*b*c^5 + 6*a^2*c^6 + 6*a*b^6*c - 15*a*b^5*c^2 - a*b^4*c^3 - 17*a*b^3*c^4 + 5*a*b^2*c^5 + 6*a*b*c^6 + 6*b^6*c^2 + 4*b^5*c^3 - 10*b^4*c^4 + 12*b^3*c^5) := by
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
  have hn : 0 ≤ (6*a^6*b^2 + 6*a^6*b*c + 4*a^5*b^3 - 15*a^5*b^2*c + 5*a^5*b*c^2 + 12*a^5*c^3 - 10*a^4*b^4 - a^4*b^3*c - 17*a^4*b*c^3 - 10*a^4*c^4 + 12*a^3*b^5 - 17*a^3*b^4*c + 10*a^3*b^3*c^2 + 10*a^3*b^2*c^3 - a^3*b*c^4 + 4*a^3*c^5 + 5*a^2*b^5*c + 10*a^2*b^3*c^3 - 15*a^2*b*c^5 + 6*a^2*c^6 + 6*a*b^6*c - 15*a*b^5*c^2 - a*b^4*c^3 - 17*a*b^3*c^4 + 5*a*b^2*c^5 + 6*a*b*c^6 + 6*b^6*c^2 + 4*b^5*c^3 - 10*b^4*c^4 + 12*b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b / (2 * c ^ 2 + a * b + b * c) + b * c / (2 * a ^ 2 + b * c + c * a) + c * a / (2 * b ^ 2 + c * a + a * b)) ≤ (3 / 4) * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a)) := @solution
#print axioms solution
