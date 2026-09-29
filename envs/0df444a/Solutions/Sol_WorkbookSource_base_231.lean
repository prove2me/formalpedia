-- Prove2me | solution 1 for WorkbookSource.base_231
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:44:29.580186+00:00
-- url     : https://prove2.me/submissions/7165978b-a1f0-4622-823c-3c4c8932b1ed

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (b + 2 * c) + b^3 / (c + 2 * a) + c^3 / (a + 2 * b)) ≥ (a^3 + b^3 + c^3) / (a + b + c)  := by
  have hp : 0 ≤ (2*a^6 + 4*a^5*b - a^5*c - 2*a^4*b*c - a^4*c^2 - 2*a^3*b*c^2 - a^2*b^4 - 2*a^2*b^3*c - a*b^5 - 2*a*b^4*c - 2*a*b^2*c^3 - 2*a*b*c^4 + 4*a*c^5 + 2*b^6 + 4*b^5*c - b^2*c^4 - b*c^5 + 2*c^6) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (33 : ℝ) * a^4 * (b - a)^2 + (33 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (33 : ℝ) * a^4 * (c - b)^2 + (76 : ℝ) * a^3 * (b - a)^3 + (84 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (120 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (56 : ℝ) * a^3 * (c - b)^3 + (72 : ℝ) * a^2 * (b - a)^4 + (84 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (150 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (138 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (42 : ℝ) * a^2 * (c - b)^4 + (33 : ℝ) * a^1 * (b - a)^5 + (39 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (78 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (108 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (66 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (15 : ℝ) * a^1 * (c - b)^5 + (6 : ℝ) * (b - a)^6 + (7 : ℝ) * (b - a)^5 * (c - b)^1 + (14 : ℝ) * (b - a)^4 * (c - b)^2 + (26 : ℝ) * (b - a)^3 * (c - b)^3 + (24 : ℝ) * (b - a)^2 * (c - b)^4 + (11 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (33 : ℝ) * a^4 * (c - a)^2 + (33 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (33 : ℝ) * a^4 * (b - c)^2 + (76 : ℝ) * a^3 * (c - a)^3 + (144 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (180 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (56 : ℝ) * a^3 * (b - c)^3 + (72 : ℝ) * a^2 * (c - a)^4 + (204 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (330 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (198 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (42 : ℝ) * a^2 * (b - c)^4 + (33 : ℝ) * a^1 * (c - a)^5 + (126 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (252 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (222 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (93 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (15 : ℝ) * a^1 * (b - c)^5 + (6 : ℝ) * (c - a)^6 + (29 : ℝ) * (c - a)^5 * (b - c)^1 + (69 : ℝ) * (c - a)^4 * (b - c)^2 + (80 : ℝ) * (c - a)^3 * (b - c)^3 + (50 : ℝ) * (c - a)^2 * (b - c)^4 + (16 : ℝ) * (c - a)^1 * (b - c)^5 + (2 : ℝ) * (b - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (33 : ℝ) * c^4 * (a - c)^2 + (33 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (33 : ℝ) * c^4 * (b - a)^2 + (76 : ℝ) * c^3 * (a - c)^3 + (84 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (120 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (56 : ℝ) * c^3 * (b - a)^3 + (72 : ℝ) * c^2 * (a - c)^4 + (84 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (150 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (138 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (42 : ℝ) * c^2 * (b - a)^4 + (33 : ℝ) * c^1 * (a - c)^5 + (39 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (78 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (108 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (66 : ℝ) * c^1 * (a - c)^1 * (b - a)^4 + (15 : ℝ) * c^1 * (b - a)^5 + (6 : ℝ) * (a - c)^6 + (7 : ℝ) * (a - c)^5 * (b - a)^1 + (14 : ℝ) * (a - c)^4 * (b - a)^2 + (26 : ℝ) * (a - c)^3 * (b - a)^3 + (24 : ℝ) * (a - c)^2 * (b - a)^4 + (11 : ℝ) * (a - c)^1 * (b - a)^5 + (2 : ℝ) * (b - a)^6 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (33 : ℝ) * b^4 * (a - b)^2 + (33 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (33 : ℝ) * b^4 * (c - a)^2 + (76 : ℝ) * b^3 * (a - b)^3 + (144 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (180 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (56 : ℝ) * b^3 * (c - a)^3 + (72 : ℝ) * b^2 * (a - b)^4 + (204 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (330 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (198 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (42 : ℝ) * b^2 * (c - a)^4 + (33 : ℝ) * b^1 * (a - b)^5 + (126 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (252 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (222 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (93 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (15 : ℝ) * b^1 * (c - a)^5 + (6 : ℝ) * (a - b)^6 + (29 : ℝ) * (a - b)^5 * (c - a)^1 + (69 : ℝ) * (a - b)^4 * (c - a)^2 + (80 : ℝ) * (a - b)^3 * (c - a)^3 + (50 : ℝ) * (a - b)^2 * (c - a)^4 + (16 : ℝ) * (a - b)^1 * (c - a)^5 + (2 : ℝ) * (c - a)^6 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (33 : ℝ) * b^4 * (c - b)^2 + (33 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (33 : ℝ) * b^4 * (a - c)^2 + (76 : ℝ) * b^3 * (c - b)^3 + (84 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (120 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (56 : ℝ) * b^3 * (a - c)^3 + (72 : ℝ) * b^2 * (c - b)^4 + (84 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (150 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (138 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (42 : ℝ) * b^2 * (a - c)^4 + (33 : ℝ) * b^1 * (c - b)^5 + (39 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (78 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (108 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (66 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (15 : ℝ) * b^1 * (a - c)^5 + (6 : ℝ) * (c - b)^6 + (7 : ℝ) * (c - b)^5 * (a - c)^1 + (14 : ℝ) * (c - b)^4 * (a - c)^2 + (26 : ℝ) * (c - b)^3 * (a - c)^3 + (24 : ℝ) * (c - b)^2 * (a - c)^4 + (11 : ℝ) * (c - b)^1 * (a - c)^5 + (2 : ℝ) * (a - c)^6 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (33 : ℝ) * c^4 * (b - c)^2 + (33 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (33 : ℝ) * c^4 * (a - b)^2 + (76 : ℝ) * c^3 * (b - c)^3 + (144 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (180 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (56 : ℝ) * c^3 * (a - b)^3 + (72 : ℝ) * c^2 * (b - c)^4 + (204 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (330 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (198 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (42 : ℝ) * c^2 * (a - b)^4 + (33 : ℝ) * c^1 * (b - c)^5 + (126 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (252 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (222 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (93 : ℝ) * c^1 * (b - c)^1 * (a - b)^4 + (15 : ℝ) * c^1 * (a - b)^5 + (6 : ℝ) * (b - c)^6 + (29 : ℝ) * (b - c)^5 * (a - b)^1 + (69 : ℝ) * (b - c)^4 * (a - b)^2 + (80 : ℝ) * (b - c)^3 * (a - b)^3 + (50 : ℝ) * (b - c)^2 * (a - b)^4 + (16 : ℝ) * (b - c)^1 * (a - b)^5 + (2 : ℝ) * (a - b)^6 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (2*a^6 + 4*a^5*b - a^5*c - 2*a^4*b*c - a^4*c^2 - 2*a^3*b*c^2 - a^2*b^4 - 2*a^2*b^3*c - a*b^5 - 2*a*b^4*c - 2*a*b^2*c^3 - 2*a*b*c^4 + 4*a*c^5 + 2*b^6 + 4*b^5*c - b^2*c^4 - b*c^5 + 2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 / (b + 2 * c) + b^3 / (c + 2 * a) + c^3 / (a + 2 * b)) ≥ (a^3 + b^3 + c^3) / (a + b + c)) := @solution
#print axioms solution
