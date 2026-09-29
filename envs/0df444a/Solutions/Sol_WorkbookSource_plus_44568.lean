-- Prove2me | solution 1 for WorkbookSource.plus_44568
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:44.548881+00:00
-- url     : https://prove2.me/submissions/7968d795-dd9c-47bb-97e6-7215d55a28e0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (8 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2) + b / (8 * b ^ 2 + 5 * c ^ 2 + 3 * a ^ 2) + c / (8 * c ^ 2 + 5 * a ^ 2 + 3 * b ^ 2)) ≤ (1 / 16) * (1 / a + 1 / b + 1 / c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (120*a^7*b + 120*a^7*c - 120*a^6*b*c + 467*a^5*b^3 - 173*a^5*b^2*c + 53*a^5*b*c^2 + 437*a^5*c^3 - 317*a^4*b^3*c - 347*a^4*b*c^3 + 437*a^3*b^5 - 347*a^3*b^4*c - 240*a^3*b^3*c^2 - 240*a^3*b^2*c^3 - 317*a^3*b*c^4 + 467*a^3*c^5 + 53*a^2*b^5*c - 240*a^2*b^3*c^3 - 173*a^2*b*c^5 + 120*a*b^7 - 120*a*b^6*c - 173*a*b^5*c^2 - 317*a*b^4*c^3 - 347*a*b^3*c^4 + 53*a*b^2*c^5 - 120*a*b*c^6 + 120*a*c^7 + 120*b^7*c + 467*b^5*c^3 + 437*b^3*c^5 + 120*b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (6016 : ℝ) * a^6 * (b - a)^2 + (6016 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (6016 : ℝ) * a^6 * (c - b)^2 + (25152 : ℝ) * a^5 * (b - a)^3 + (38136 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (34872 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (10944 : ℝ) * a^5 * (c - b)^3 + (45376 : ℝ) * a^4 * (b - a)^4 + (92112 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (94488 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (47752 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (9856 : ℝ) * a^4 * (c - b)^4 + (45200 : ℝ) * a^3 * (b - a)^5 + (114670 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (138268 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (91372 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (32782 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (5104 : ℝ) * a^3 * (c - b)^5 + (26184 : ℝ) * a^2 * (b - a)^6 + (79414 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (112135 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (90900 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (44399 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (12404 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1560 : ℝ) * a^2 * (c - b)^6 + (8368 : ℝ) * a^1 * (b - a)^7 + (29402 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (47790 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (45810 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (27858 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (10724 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2400 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (240 : ℝ) * a^1 * (c - b)^7 + (1144 : ℝ) * (b - a)^8 + (4546 : ℝ) * (b - a)^7 * (c - b)^1 + (8291 : ℝ) * (b - a)^6 * (c - b)^2 + (9037 : ℝ) * (b - a)^5 * (c - b)^3 + (6385 : ℝ) * (b - a)^4 * (c - b)^4 + (2957 : ℝ) * (b - a)^3 * (c - b)^5 + (840 : ℝ) * (b - a)^2 * (c - b)^6 + (120 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (120*a^7*b + 120*a^7*c - 120*a^6*b*c + 467*a^5*b^3 - 173*a^5*b^2*c + 53*a^5*b*c^2 + 437*a^5*c^3 - 317*a^4*b^3*c - 347*a^4*b*c^3 + 437*a^3*b^5 - 347*a^3*b^4*c - 240*a^3*b^3*c^2 - 240*a^3*b^2*c^3 - 317*a^3*b*c^4 + 467*a^3*c^5 + 53*a^2*b^5*c - 240*a^2*b^3*c^3 - 173*a^2*b*c^5 + 120*a*b^7 - 120*a*b^6*c - 173*a*b^5*c^2 - 317*a*b^4*c^3 - 347*a*b^3*c^4 + 53*a*b^2*c^5 - 120*a*b*c^6 + 120*a*c^7 + 120*b^7*c + 467*b^5*c^3 + 437*b^3*c^5 + 120*b*c^7) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (6016 : ℝ) * a^6 * (c - a)^2 + (6016 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (6016 : ℝ) * a^6 * (b - c)^2 + (25152 : ℝ) * a^5 * (c - a)^3 + (37320 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (34056 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (10944 : ℝ) * a^5 * (b - c)^3 + (45376 : ℝ) * a^4 * (c - a)^4 + (89392 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (90408 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (46392 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (9856 : ℝ) * a^4 * (b - c)^4 + (45200 : ℝ) * a^3 * (c - a)^5 + (111330 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (131588 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (87412 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (32162 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (5104 : ℝ) * a^3 * (b - c)^5 + (26184 : ℝ) * a^2 * (c - a)^6 + (77690 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (107825 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (87180 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (43129 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (12268 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (1560 : ℝ) * a^2 * (b - c)^6 + (8368 : ℝ) * a^1 * (c - a)^7 + (29174 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (47106 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (44990 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (27358 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (10588 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (2400 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (240 : ℝ) * a^1 * (b - c)^7 + (1144 : ℝ) * (c - a)^8 + (4606 : ℝ) * (c - a)^7 * (b - c)^1 + (8501 : ℝ) * (c - a)^6 * (b - c)^2 + (9307 : ℝ) * (c - a)^5 * (b - c)^3 + (6535 : ℝ) * (c - a)^4 * (b - c)^4 + (2987 : ℝ) * (c - a)^3 * (b - c)^5 + (840 : ℝ) * (c - a)^2 * (b - c)^6 + (120 : ℝ) * (c - a)^1 * (b - c)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (120*a^7*b + 120*a^7*c - 120*a^6*b*c + 467*a^5*b^3 - 173*a^5*b^2*c + 53*a^5*b*c^2 + 437*a^5*c^3 - 317*a^4*b^3*c - 347*a^4*b*c^3 + 437*a^3*b^5 - 347*a^3*b^4*c - 240*a^3*b^3*c^2 - 240*a^3*b^2*c^3 - 317*a^3*b*c^4 + 467*a^3*c^5 + 53*a^2*b^5*c - 240*a^2*b^3*c^3 - 173*a^2*b*c^5 + 120*a*b^7 - 120*a*b^6*c - 173*a*b^5*c^2 - 317*a*b^4*c^3 - 347*a*b^3*c^4 + 53*a*b^2*c^5 - 120*a*b*c^6 + 120*a*c^7 + 120*b^7*c + 467*b^5*c^3 + 437*b^3*c^5 + 120*b*c^7) := by
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
  have hn : 0 ≤ (120*a^7*b + 120*a^7*c - 120*a^6*b*c + 467*a^5*b^3 - 173*a^5*b^2*c + 53*a^5*b*c^2 + 437*a^5*c^3 - 317*a^4*b^3*c - 347*a^4*b*c^3 + 437*a^3*b^5 - 347*a^3*b^4*c - 240*a^3*b^3*c^2 - 240*a^3*b^2*c^3 - 317*a^3*b*c^4 + 467*a^3*c^5 + 53*a^2*b^5*c - 240*a^2*b^3*c^3 - 173*a^2*b*c^5 + 120*a*b^7 - 120*a*b^6*c - 173*a*b^5*c^2 - 317*a*b^4*c^3 - 347*a*b^3*c^4 + 53*a*b^2*c^5 - 120*a*b*c^6 + 120*a*c^7 + 120*b^7*c + 467*b^5*c^3 + 437*b^3*c^5 + 120*b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (8 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2) + b / (8 * b ^ 2 + 5 * c ^ 2 + 3 * a ^ 2) + c / (8 * c ^ 2 + 5 * a ^ 2 + 3 * b ^ 2)) ≤ (1 / 16) * (1 / a + 1 / b + 1 / c)) := @solution
#print axioms solution
