-- Prove2me | solution 1 for WorkbookSource.base_18984
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:37:21.991949+00:00
-- url     : https://prove2.me/submissions/e3c72d93-dc55-4a9a-b4c1-ff47ffa9ce8d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b + c) + b^2 / (a + c) + c^2 / (a + b) + (3 * (a * b + b * c + a * c)) / (2 * (a + b + c))) ≥ (a + b + c)^3 / (3 * (a * b + b * c + a * c))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6*b + 4*a^6*c + 2*a^5*b^2 + 10*a^5*b*c + 2*a^5*c^2 - 5*a^4*b^3 + a^4*b^2*c + a^4*b*c^2 - 5*a^4*c^3 - 5*a^3*b^4 - 10*a^3*b^3*c - 4*a^3*b^2*c^2 - 10*a^3*b*c^3 - 5*a^3*c^4 + 2*a^2*b^5 + a^2*b^4*c - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 + a^2*b*c^4 + 2*a^2*c^5 + 4*a*b^6 + 10*a*b^5*c + a*b^4*c^2 - 10*a*b^3*c^3 + a*b^2*c^4 + 10*a*b*c^5 + 4*a*c^6 + 4*b^6*c + 2*b^5*c^2 - 5*b^4*c^3 - 5*b^3*c^4 + 2*b^2*c^5 + 4*b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (108 : ℝ) * a^5 * (b - a)^2 + (108 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (108 : ℝ) * a^5 * (c - b)^2 + (306 : ℝ) * a^4 * (b - a)^3 + (459 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (621 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (234 : ℝ) * a^4 * (c - b)^3 + (326 : ℝ) * a^3 * (b - a)^4 + (652 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (1158 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (832 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (182 : ℝ) * a^3 * (c - b)^4 + (160 : ℝ) * a^2 * (b - a)^5 + (400 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (928 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (992 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (428 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (62 : ℝ) * a^2 * (c - b)^5 + (34 : ℝ) * a^1 * (b - a)^6 + (102 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (322 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (474 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (306 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (86 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (8 : ℝ) * a^1 * (c - b)^6 + (2 : ℝ) * (b - a)^7 + (7 : ℝ) * (b - a)^6 * (c - b)^1 + (37 : ℝ) * (b - a)^5 * (c - b)^2 + (75 : ℝ) * (b - a)^4 * (c - b)^3 + (65 : ℝ) * (b - a)^3 * (c - b)^4 + (26 : ℝ) * (b - a)^2 * (c - b)^5 + (4 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6*b + 4*a^6*c + 2*a^5*b^2 + 10*a^5*b*c + 2*a^5*c^2 - 5*a^4*b^3 + a^4*b^2*c + a^4*b*c^2 - 5*a^4*c^3 - 5*a^3*b^4 - 10*a^3*b^3*c - 4*a^3*b^2*c^2 - 10*a^3*b*c^3 - 5*a^3*c^4 + 2*a^2*b^5 + a^2*b^4*c - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 + a^2*b*c^4 + 2*a^2*c^5 + 4*a*b^6 + 10*a*b^5*c + a*b^4*c^2 - 10*a*b^3*c^3 + a*b^2*c^4 + 10*a*b*c^5 + 4*a*c^6 + 4*b^6*c + 2*b^5*c^2 - 5*b^4*c^3 - 5*b^3*c^4 + 2*b^2*c^5 + 4*b*c^6) := by
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
  have hn : 0 ≤ (4*a^6*b + 4*a^6*c + 2*a^5*b^2 + 10*a^5*b*c + 2*a^5*c^2 - 5*a^4*b^3 + a^4*b^2*c + a^4*b*c^2 - 5*a^4*c^3 - 5*a^3*b^4 - 10*a^3*b^3*c - 4*a^3*b^2*c^2 - 10*a^3*b*c^3 - 5*a^3*c^4 + 2*a^2*b^5 + a^2*b^4*c - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 + a^2*b*c^4 + 2*a^2*c^5 + 4*a*b^6 + 10*a*b^5*c + a*b^4*c^2 - 10*a*b^3*c^3 + a*b^2*c^4 + 10*a*b*c^5 + 4*a*c^6 + 4*b^6*c + 2*b^5*c^2 - 5*b^4*c^3 - 5*b^3*c^4 + 2*b^2*c^5 + 4*b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (b + c) + b^2 / (a + c) + c^2 / (a + b) + (3 * (a * b + b * c + a * c)) / (2 * (a + b + c))) ≥ (a + b + c)^3 / (3 * (a * b + b * c + a * c))) := @solution
#print axioms solution
