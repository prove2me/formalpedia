-- Prove2me | solution 1 for WorkbookSource.base_8366
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:38:16.953137+00:00
-- url     : https://prove2.me/submissions/b17e588d-ad06-4e82-af29-18ca9d5efbc3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (2 * a * b * c) + (2 * a * b * c) / (a^3 + b^3 + c^3) ≥ (a + b) / (b + c) + (b + c) / (a + b) + 1 / 6  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^7*b + 3*a^7*c + 3*a^6*b^2 - 3*a^6*b*c - 13*a^5*b^2*c - a^5*b*c^2 + 6*a^4*b^4 - 7*a^4*b^3*c - 13*a^4*b^2*c^2 + 6*a^4*c^4 + 6*a^3*b^5 + 12*a^3*b^3*c^2 + 18*a^3*b^2*c^3 - 13*a^2*b^5*c + 11*a^2*b^4*c^2 + 12*a^2*b^3*c^3 - 13*a^2*b^2*c^4 - a^2*b*c^5 + 3*a*b^7 - 10*a*b^6*c - 13*a*b^5*c^2 - 7*a*b^3*c^4 - 13*a*b^2*c^5 - 3*a*b*c^6 + 3*a*c^7 + 3*b^8 + 3*b^7*c + 6*b^5*c^3 + 6*b^4*c^4 + 3*b^2*c^6 + 3*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (42 : ℝ) * a^6 * (b - a)^2 + (24 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (42 : ℝ) * a^6 * (c - b)^2 + (178 : ℝ) * a^5 * (b - a)^3 + (180 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (216 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (74 : ℝ) * a^5 * (c - b)^3 + (392 : ℝ) * a^4 * (b - a)^4 + (603 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (735 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (433 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (132 : ℝ) * a^4 * (c - b)^4 + (516 : ℝ) * a^3 * (b - a)^5 + (1068 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1472 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1140 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (552 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (112 : ℝ) * a^3 * (c - b)^5 + (388 : ℝ) * a^2 * (b - a)^6 + (996 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1554 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1448 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (882 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (306 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (42 : ℝ) * a^2 * (c - b)^6 + (152 : ℝ) * a^1 * (b - a)^7 + (462 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (805 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (862 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (612 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (275 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (66 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (6 : ℝ) * a^1 * (c - b)^7 + (24 : ℝ) * (b - a)^8 + (84 : ℝ) * (b - a)^7 * (c - b)^1 + (162 : ℝ) * (b - a)^6 * (c - b)^2 + (195 : ℝ) * (b - a)^5 * (c - b)^3 + (156 : ℝ) * (b - a)^4 * (c - b)^4 + (81 : ℝ) * (b - a)^3 * (c - b)^5 + (24 : ℝ) * (b - a)^2 * (c - b)^6 + (3 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^7*b + 3*a^7*c + 3*a^6*b^2 - 3*a^6*b*c - 13*a^5*b^2*c - a^5*b*c^2 + 6*a^4*b^4 - 7*a^4*b^3*c - 13*a^4*b^2*c^2 + 6*a^4*c^4 + 6*a^3*b^5 + 12*a^3*b^3*c^2 + 18*a^3*b^2*c^3 - 13*a^2*b^5*c + 11*a^2*b^4*c^2 + 12*a^2*b^3*c^3 - 13*a^2*b^2*c^4 - a^2*b*c^5 + 3*a*b^7 - 10*a*b^6*c - 13*a*b^5*c^2 - 7*a*b^3*c^4 - 13*a*b^2*c^5 - 3*a*b*c^6 + 3*a*c^7 + 3*b^8 + 3*b^7*c + 6*b^5*c^3 + 6*b^4*c^4 + 3*b^2*c^6 + 3*b*c^7) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (42 : ℝ) * a^6 * (c - a)^2 + (60 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (60 : ℝ) * a^6 * (b - c)^2 + (178 : ℝ) * a^5 * (c - a)^3 + (354 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (390 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (140 : ℝ) * a^5 * (b - c)^3 + (392 : ℝ) * a^4 * (c - a)^4 + (965 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (1278 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (796 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (223 : ℝ) * a^4 * (b - c)^4 + (516 : ℝ) * a^3 * (c - a)^5 + (1512 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (2360 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (2028 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (996 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (220 : ℝ) * a^3 * (b - c)^5 + (388 : ℝ) * a^2 * (c - a)^6 + (1332 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (2394 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (2568 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (1722 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (678 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (116 : ℝ) * a^2 * (b - c)^6 + (152 : ℝ) * a^1 * (c - a)^7 + (602 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (1225 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (1553 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (1294 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (701 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (221 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (30 : ℝ) * a^1 * (b - c)^7 + (24 : ℝ) * (c - a)^8 + (108 : ℝ) * (c - a)^7 * (b - c)^1 + (246 : ℝ) * (c - a)^6 * (b - c)^2 + (357 : ℝ) * (c - a)^5 * (b - c)^3 + (351 : ℝ) * (c - a)^4 * (b - c)^4 + (237 : ℝ) * (c - a)^3 * (b - c)^5 + (105 : ℝ) * (c - a)^2 * (b - c)^6 + (27 : ℝ) * (c - a)^1 * (b - c)^7 + (3 : ℝ) * (b - c)^8 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ a) (hord2 : a ≤ c) : 0 ≤ (3*a^7*b + 3*a^7*c + 3*a^6*b^2 - 3*a^6*b*c - 13*a^5*b^2*c - a^5*b*c^2 + 6*a^4*b^4 - 7*a^4*b^3*c - 13*a^4*b^2*c^2 + 6*a^4*c^4 + 6*a^3*b^5 + 12*a^3*b^3*c^2 + 18*a^3*b^2*c^3 - 13*a^2*b^5*c + 11*a^2*b^4*c^2 + 12*a^2*b^3*c^3 - 13*a^2*b^2*c^4 - a^2*b*c^5 + 3*a*b^7 - 10*a*b^6*c - 13*a*b^5*c^2 - 7*a*b^3*c^4 - 13*a*b^2*c^5 - 3*a*b*c^6 + 3*a*c^7 + 3*b^8 + 3*b^7*c + 6*b^5*c^3 + 6*b^4*c^4 + 3*b^2*c^6 + 3*b*c^7) := by
    have hdiff1 : 0 ≤ (a - b) := by linarith
    have hdiff2 : 0 ≤ (c - a) := by linarith
    have hpos : 0 ≤ (60 : ℝ) * b^6 * (a - b)^2 + (60 : ℝ) * b^6 * (a - b)^1 * (c - a)^1 + (42 : ℝ) * b^6 * (c - a)^2 + (220 : ℝ) * b^5 * (a - b)^3 + (330 : ℝ) * b^5 * (a - b)^2 * (c - a)^1 + (258 : ℝ) * b^5 * (a - b)^1 * (c - a)^2 + (74 : ℝ) * b^5 * (c - a)^3 + (423 : ℝ) * b^4 * (a - b)^4 + (846 : ℝ) * b^4 * (a - b)^3 * (c - a)^1 + (888 : ℝ) * b^4 * (a - b)^2 * (c - a)^2 + (465 : ℝ) * b^4 * (a - b)^1 * (c - a)^3 + (132 : ℝ) * b^4 * (c - a)^4 + (472 : ℝ) * b^3 * (a - b)^5 + (1180 : ℝ) * b^3 * (a - b)^4 * (c - a)^1 + (1568 : ℝ) * b^3 * (a - b)^3 * (c - a)^2 + (1172 : ℝ) * b^3 * (a - b)^2 * (c - a)^3 + (536 : ℝ) * b^3 * (a - b)^1 * (c - a)^4 + (112 : ℝ) * b^3 * (c - a)^5 + (294 : ℝ) * b^2 * (a - b)^6 + (882 : ℝ) * b^2 * (a - b)^5 * (c - a)^1 + (1398 : ℝ) * b^2 * (a - b)^4 * (c - a)^2 + (1326 : ℝ) * b^2 * (a - b)^3 * (c - a)^3 + (798 : ℝ) * b^2 * (a - b)^2 * (c - a)^4 + (282 : ℝ) * b^2 * (a - b)^1 * (c - a)^5 + (42 : ℝ) * b^2 * (c - a)^6 + (94 : ℝ) * b^1 * (a - b)^7 + (329 : ℝ) * b^1 * (a - b)^6 * (c - a)^1 + (601 : ℝ) * b^1 * (a - b)^5 * (c - a)^2 + (680 : ℝ) * b^1 * (a - b)^4 * (c - a)^3 + (499 : ℝ) * b^1 * (a - b)^3 * (c - a)^4 + (233 : ℝ) * b^1 * (a - b)^2 * (c - a)^5 + (60 : ℝ) * b^1 * (a - b)^1 * (c - a)^6 + (6 : ℝ) * b^1 * (c - a)^7 + (12 : ℝ) * (a - b)^8 + (48 : ℝ) * (a - b)^7 * (c - a)^1 + (99 : ℝ) * (a - b)^6 * (c - a)^2 + (129 : ℝ) * (a - b)^5 * (c - a)^3 + (111 : ℝ) * (a - b)^4 * (c - a)^4 + (63 : ℝ) * (a - b)^3 * (c - a)^5 + (21 : ℝ) * (a - b)^2 * (c - a)^6 + (3 : ℝ) * (a - b)^1 * (c - a)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^7*b + 3*a^7*c + 3*a^6*b^2 - 3*a^6*b*c - 13*a^5*b^2*c - a^5*b*c^2 + 6*a^4*b^4 - 7*a^4*b^3*c - 13*a^4*b^2*c^2 + 6*a^4*c^4 + 6*a^3*b^5 + 12*a^3*b^3*c^2 + 18*a^3*b^2*c^3 - 13*a^2*b^5*c + 11*a^2*b^4*c^2 + 12*a^2*b^3*c^3 - 13*a^2*b^2*c^4 - a^2*b*c^5 + 3*a*b^7 - 10*a*b^6*c - 13*a*b^5*c^2 - 7*a*b^3*c^4 - 13*a*b^2*c^5 - 3*a*b*c^6 + 3*a*c^7 + 3*b^8 + 3*b^7*c + 6*b^5*c^3 + 6*b^4*c^4 + 3*b^2*c^6 + 3*b*c^7) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux2 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (3*a^7*b + 3*a^7*c + 3*a^6*b^2 - 3*a^6*b*c - 13*a^5*b^2*c - a^5*b*c^2 + 6*a^4*b^4 - 7*a^4*b^3*c - 13*a^4*b^2*c^2 + 6*a^4*c^4 + 6*a^3*b^5 + 12*a^3*b^3*c^2 + 18*a^3*b^2*c^3 - 13*a^2*b^5*c + 11*a^2*b^4*c^2 + 12*a^2*b^3*c^3 - 13*a^2*b^2*c^4 - a^2*b*c^5 + 3*a*b^7 - 10*a*b^6*c - 13*a*b^5*c^2 - 7*a*b^3*c^4 - 13*a*b^2*c^5 - 3*a*b*c^6 + 3*a*c^7 + 3*b^8 + 3*b^7*c + 6*b^5*c^3 + 6*b^4*c^4 + 3*b^2*c^6 + 3*b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3 + c^3) / (2 * a * b * c) + (2 * a * b * c) / (a^3 + b^3 + c^3) ≥ (a + b) / (b + c) + (b + c) / (a + b) + 1 / 6) := @solution
#print axioms solution
