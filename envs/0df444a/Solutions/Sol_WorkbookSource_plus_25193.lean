-- Prove2me | solution 1 for WorkbookSource.plus_25193
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:45:05.948183+00:00
-- url     : https://prove2.me/submissions/2ac0b900-53f4-4cfc-9f7e-72a89b1d4bb9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (3 * a ^ 2 + 3 * b ^ 2 + 2 * c ^ 2) + b * c / (3 * b ^ 2 + 3 * c ^ 2 + 2 * a ^ 2) + c * a / (3 * c ^ 2 + 3 * a ^ 2 + 2 * b ^ 2)) ≤ (a + b + c) ^ 2 / (8 * (a ^ 2 + b ^ 2 + c ^ 2))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (18*a^8 - 12*a^7*b - 12*a^7*c + 75*a^6*b^2 - 36*a^6*b*c + 75*a^6*c^2 - 38*a^5*b^3 - 54*a^5*b^2*c - 54*a^5*b*c^2 - 38*a^5*c^3 + 114*a^4*b^4 - 78*a^4*b^3*c + 230*a^4*b^2*c^2 - 78*a^4*b*c^3 + 114*a^4*c^4 - 38*a^3*b^5 - 78*a^3*b^4*c - 112*a^3*b^3*c^2 - 112*a^3*b^2*c^3 - 78*a^3*b*c^4 - 38*a^3*c^5 + 75*a^2*b^6 - 54*a^2*b^5*c + 230*a^2*b^4*c^2 - 112*a^2*b^3*c^3 + 230*a^2*b^2*c^4 - 54*a^2*b*c^5 + 75*a^2*c^6 - 12*a*b^7 - 36*a*b^6*c - 54*a*b^5*c^2 - 78*a*b^4*c^3 - 78*a*b^3*c^4 - 54*a*b^2*c^5 - 36*a*b*c^6 - 12*a*c^7 + 18*b^8 - 12*b^7*c + 75*b^6*c^2 - 38*b^5*c^3 + 114*b^4*c^4 - 38*b^3*c^5 + 75*b^2*c^6 - 12*b*c^7 + 18*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (704 : ℝ) * a^6 * (b - a)^2 + (704 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (704 : ℝ) * a^6 * (c - b)^2 + (2864 : ℝ) * a^5 * (b - a)^3 + (4296 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (4152 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (1360 : ℝ) * a^5 * (c - b)^3 + (5272 : ℝ) * a^4 * (b - a)^4 + (10544 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (11696 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (6424 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (1512 : ℝ) * a^4 * (c - b)^4 + (5524 : ℝ) * a^3 * (b - a)^5 + (13810 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (18100 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (13340 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (5534 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (1004 : ℝ) * a^3 * (c - b)^5 + (3470 : ℝ) * a^2 * (b - a)^6 + (10410 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (16049 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (14748 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (8495 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (2856 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (450 : ℝ) * a^2 * (c - b)^6 + (1240 : ℝ) * a^1 * (b - a)^7 + (4340 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (7764 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (8560 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (6248 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (2982 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (870 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (120 : ℝ) * a^1 * (c - b)^7 + (200 : ℝ) * (b - a)^8 + (800 : ℝ) * (b - a)^7 * (c - b)^1 + (1642 : ℝ) * (b - a)^6 * (c - b)^2 + (2126 : ℝ) * (b - a)^5 * (c - b)^3 + (1889 : ℝ) * (b - a)^4 * (c - b)^4 + (1168 : ℝ) * (b - a)^3 * (c - b)^5 + (495 : ℝ) * (b - a)^2 * (c - b)^6 + (132 : ℝ) * (b - a)^1 * (c - b)^7 + (18 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (18*a^8 - 12*a^7*b - 12*a^7*c + 75*a^6*b^2 - 36*a^6*b*c + 75*a^6*c^2 - 38*a^5*b^3 - 54*a^5*b^2*c - 54*a^5*b*c^2 - 38*a^5*c^3 + 114*a^4*b^4 - 78*a^4*b^3*c + 230*a^4*b^2*c^2 - 78*a^4*b*c^3 + 114*a^4*c^4 - 38*a^3*b^5 - 78*a^3*b^4*c - 112*a^3*b^3*c^2 - 112*a^3*b^2*c^3 - 78*a^3*b*c^4 - 38*a^3*c^5 + 75*a^2*b^6 - 54*a^2*b^5*c + 230*a^2*b^4*c^2 - 112*a^2*b^3*c^3 + 230*a^2*b^2*c^4 - 54*a^2*b*c^5 + 75*a^2*c^6 - 12*a*b^7 - 36*a*b^6*c - 54*a*b^5*c^2 - 78*a*b^4*c^3 - 78*a*b^3*c^4 - 54*a*b^2*c^5 - 36*a*b*c^6 - 12*a*c^7 + 18*b^8 - 12*b^7*c + 75*b^6*c^2 - 38*b^5*c^3 + 114*b^4*c^4 - 38*b^3*c^5 + 75*b^2*c^6 - 12*b*c^7 + 18*c^8) := by
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
  have hn : 0 ≤ (18*a^8 - 12*a^7*b - 12*a^7*c + 75*a^6*b^2 - 36*a^6*b*c + 75*a^6*c^2 - 38*a^5*b^3 - 54*a^5*b^2*c - 54*a^5*b*c^2 - 38*a^5*c^3 + 114*a^4*b^4 - 78*a^4*b^3*c + 230*a^4*b^2*c^2 - 78*a^4*b*c^3 + 114*a^4*c^4 - 38*a^3*b^5 - 78*a^3*b^4*c - 112*a^3*b^3*c^2 - 112*a^3*b^2*c^3 - 78*a^3*b*c^4 - 38*a^3*c^5 + 75*a^2*b^6 - 54*a^2*b^5*c + 230*a^2*b^4*c^2 - 112*a^2*b^3*c^3 + 230*a^2*b^2*c^4 - 54*a^2*b*c^5 + 75*a^2*c^6 - 12*a*b^7 - 36*a*b^6*c - 54*a*b^5*c^2 - 78*a*b^4*c^3 - 78*a*b^3*c^4 - 54*a*b^2*c^5 - 36*a*b*c^6 - 12*a*c^7 + 18*b^8 - 12*b^7*c + 75*b^6*c^2 - 38*b^5*c^3 + 114*b^4*c^4 - 38*b^3*c^5 + 75*b^2*c^6 - 12*b*c^7 + 18*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b / (3 * a ^ 2 + 3 * b ^ 2 + 2 * c ^ 2) + b * c / (3 * b ^ 2 + 3 * c ^ 2 + 2 * a ^ 2) + c * a / (3 * c ^ 2 + 3 * a ^ 2 + 2 * b ^ 2)) ≤ (a + b + c) ^ 2 / (8 * (a ^ 2 + b ^ 2 + c ^ 2))) := @solution
#print axioms solution
