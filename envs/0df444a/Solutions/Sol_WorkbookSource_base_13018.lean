-- Prove2me | solution 1 for WorkbookSource.base_13018
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:05.447189+00:00
-- url     : https://prove2.me/submissions/12022139-345c-4fba-8f97-f938f6083a2d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ 1 + 1 / 3 * ( (a / (a + b) - b / (b + c))^2 + (b / (b + c) - c / (c + a))^2 + (c / (c + a) - a / (a + b))^2 )  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 + a^5*b^3 + 5*a^5*b^2*c + 5*a^5*b*c^2 + a^5*c^3 - 2*a^4*b^4 - 5*a^4*b^3*c - 4*a^4*b^2*c^2 - 5*a^4*b*c^3 - 2*a^4*c^4 + a^3*b^5 - 5*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 - 5*a^3*b*c^4 + a^3*c^5 + 3*a^2*b^6 + 5*a^2*b^5*c - 4*a^2*b^4*c^2 - 8*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 5*a^2*b*c^5 + 3*a^2*c^6 + 6*a*b^6*c + 5*a*b^5*c^2 - 5*a*b^4*c^3 - 5*a*b^3*c^4 + 5*a*b^2*c^5 + 6*a*b*c^6 + 3*b^6*c^2 + b^5*c^3 - 2*b^4*c^4 + b^3*c^5 + 3*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (120 : ℝ) * a^6 * (b - a)^2 + (120 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (120 : ℝ) * a^6 * (c - b)^2 + (456 : ℝ) * a^5 * (b - a)^3 + (684 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (756 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (264 : ℝ) * a^5 * (c - b)^3 + (702 : ℝ) * a^4 * (b - a)^4 + (1404 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1806 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (1104 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (222 : ℝ) * a^4 * (c - b)^4 + (564 : ℝ) * a^3 * (b - a)^5 + (1410 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (2100 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1740 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (654 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (84 : ℝ) * a^3 * (c - b)^5 + (252 : ℝ) * a^2 * (b - a)^6 + (756 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1278 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1296 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (684 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (162 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (12 : ℝ) * a^2 * (c - b)^6 + (60 : ℝ) * a^1 * (b - a)^7 + (210 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (394 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (460 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (302 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (98 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (12 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (6 : ℝ) * (b - a)^8 + (24 : ℝ) * (b - a)^7 * (c - b)^1 + (49 : ℝ) * (b - a)^6 * (c - b)^2 + (63 : ℝ) * (b - a)^5 * (c - b)^3 + (48 : ℝ) * (b - a)^4 * (c - b)^4 + (19 : ℝ) * (b - a)^3 * (c - b)^5 + (3 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 + a^5*b^3 + 5*a^5*b^2*c + 5*a^5*b*c^2 + a^5*c^3 - 2*a^4*b^4 - 5*a^4*b^3*c - 4*a^4*b^2*c^2 - 5*a^4*b*c^3 - 2*a^4*c^4 + a^3*b^5 - 5*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 - 5*a^3*b*c^4 + a^3*c^5 + 3*a^2*b^6 + 5*a^2*b^5*c - 4*a^2*b^4*c^2 - 8*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 5*a^2*b*c^5 + 3*a^2*c^6 + 6*a*b^6*c + 5*a*b^5*c^2 - 5*a*b^4*c^3 - 5*a*b^3*c^4 + 5*a*b^2*c^5 + 6*a*b*c^6 + 3*b^6*c^2 + b^5*c^3 - 2*b^4*c^4 + b^3*c^5 + 3*b^2*c^6) := by
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
  have hn : 0 ≤ (3*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 + a^5*b^3 + 5*a^5*b^2*c + 5*a^5*b*c^2 + a^5*c^3 - 2*a^4*b^4 - 5*a^4*b^3*c - 4*a^4*b^2*c^2 - 5*a^4*b*c^3 - 2*a^4*c^4 + a^3*b^5 - 5*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 - 5*a^3*b*c^4 + a^3*c^5 + 3*a^2*b^6 + 5*a^2*b^5*c - 4*a^2*b^4*c^2 - 8*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 5*a^2*b*c^5 + 3*a^2*c^6 + 6*a*b^6*c + 5*a*b^5*c^2 - 5*a*b^4*c^3 - 5*a*b^3*c^4 + 5*a*b^2*c^5 + 6*a*b*c^6 + 3*b^6*c^2 + b^5*c^3 - 2*b^4*c^4 + b^3*c^5 + 3*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ 1 + 1 / 3 * ( (a / (a + b) - b / (b + c))^2 + (b / (b + c) - c / (c + a))^2 + (c / (c + a) - a / (a + b))^2 )) := @solution
#print axioms solution
