-- Prove2me | solution 1 for WorkbookSource.base_8606
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:39:29.231231+00:00
-- url     : https://prove2.me/submissions/82364b01-bb32-4bc7-afb1-ff6f12b73b85

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (6 * a) / (9 * a ^ 2 + 5 * (a + b + c) ^ 2) + (6 * b) / (9 * b ^ 2 + 5 * (a + b + c) ^ 2) + (6 * c) / (9 * c ^ 2 + 5 * (a + b + c) ^ 2) ≤ 1 / (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (200*a^6 + 480*a^5*b + 480*a^5*c + 525*a^4*b^2 + 330*a^4*b*c + 525*a^4*c^2 + 490*a^3*b^3 - 1086*a^3*b^2*c - 1086*a^3*b*c^2 + 490*a^3*c^3 + 525*a^2*b^4 - 1086*a^2*b^3*c - 2574*a^2*b^2*c^2 - 1086*a^2*b*c^3 + 525*a^2*c^4 + 480*a*b^5 + 330*a*b^4*c - 1086*a*b^3*c^2 - 1086*a*b^2*c^3 + 330*a*b*c^4 + 480*a*c^5 + 200*b^6 + 480*b^5*c + 525*b^4*c^2 + 490*b^3*c^3 + 525*b^2*c^4 + 480*b*c^5 + 200*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (13608 : ℝ) * a^4 * (b - a)^2 + (13608 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (13608 : ℝ) * a^4 * (c - b)^2 + (36504 : ℝ) * a^3 * (b - a)^3 + (54756 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (54108 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (17928 : ℝ) * a^3 * (c - b)^3 + (37044 : ℝ) * a^2 * (b - a)^4 + (74088 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (82296 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (45252 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (9180 : ℝ) * a^2 * (c - b)^4 + (16848 : ℝ) * a^1 * (b - a)^5 + (42120 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (54216 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (39204 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (14580 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2160 : ℝ) * a^1 * (c - b)^5 + (2900 : ℝ) * (b - a)^6 + (8700 : ℝ) * (b - a)^5 * (c - b)^1 + (12945 : ℝ) * (b - a)^4 * (c - b)^2 + (11390 : ℝ) * (b - a)^3 * (c - b)^3 + (5925 : ℝ) * (b - a)^2 * (c - b)^4 + (1680 : ℝ) * (b - a)^1 * (c - b)^5 + (200 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (200*a^6 + 480*a^5*b + 480*a^5*c + 525*a^4*b^2 + 330*a^4*b*c + 525*a^4*c^2 + 490*a^3*b^3 - 1086*a^3*b^2*c - 1086*a^3*b*c^2 + 490*a^3*c^3 + 525*a^2*b^4 - 1086*a^2*b^3*c - 2574*a^2*b^2*c^2 - 1086*a^2*b*c^3 + 525*a^2*c^4 + 480*a*b^5 + 330*a*b^4*c - 1086*a*b^3*c^2 - 1086*a*b^2*c^3 + 330*a*b*c^4 + 480*a*c^5 + 200*b^6 + 480*b^5*c + 525*b^4*c^2 + 490*b^3*c^3 + 525*b^2*c^4 + 480*b*c^5 + 200*c^6) := by
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
  have hn : 0 ≤ (200*a^6 + 480*a^5*b + 480*a^5*c + 525*a^4*b^2 + 330*a^4*b*c + 525*a^4*c^2 + 490*a^3*b^3 - 1086*a^3*b^2*c - 1086*a^3*b*c^2 + 490*a^3*c^3 + 525*a^2*b^4 - 1086*a^2*b^3*c - 2574*a^2*b^2*c^2 - 1086*a^2*b*c^3 + 525*a^2*c^4 + 480*a*b^5 + 330*a*b^4*c - 1086*a*b^3*c^2 - 1086*a*b^2*c^3 + 330*a*b*c^4 + 480*a*c^5 + 200*b^6 + 480*b^5*c + 525*b^4*c^2 + 490*b^3*c^3 + 525*b^2*c^4 + 480*b*c^5 + 200*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (6 * a) / (9 * a ^ 2 + 5 * (a + b + c) ^ 2) + (6 * b) / (9 * b ^ 2 + 5 * (a + b + c) ^ 2) + (6 * c) / (9 * c ^ 2 + 5 * (a + b + c) ^ 2) ≤ 1 / (a + b + c)) := @solution
#print axioms solution
