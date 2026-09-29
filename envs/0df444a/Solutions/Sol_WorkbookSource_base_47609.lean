-- Prove2me | solution 1 for WorkbookSource.base_47609
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:21:23.877804+00:00
-- url     : https://prove2.me/submissions/16b414d3-8577-4fd1-8915-4eea89a0359a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 3 * b^2) / (b + c)^2 + (b^2 + 3 * c^2) / (c + a)^2 + (c^2 + 3 * a^2) / (a + b)^2 - 1 ≥ 2 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7*b + a^7*c + a^6*b*c + 2*a^5*b^3 + 4*a^5*b^2*c + a^5*b*c^2 - a^5*c^3 + 2*a^4*b^3*c - a^4*b*c^3 - a^3*b^5 - a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 + 2*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^5*c - 10*a^2*b^3*c^3 + 4*a^2*b*c^5 + a*b^7 + a*b^6*c + 4*a*b^5*c^2 + 2*a*b^4*c^3 - a*b^3*c^4 + a*b^2*c^5 + a*b*c^6 + a*c^7 + b^7*c + 2*b^5*c^3 - b^3*c^5 + b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * a^6 * (b - a)^2 + (64 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (64 : ℝ) * a^6 * (c - b)^2 + (248 : ℝ) * a^5 * (b - a)^3 + (336 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (360 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (136 : ℝ) * a^5 * (c - b)^3 + (396 : ℝ) * a^4 * (b - a)^4 + (672 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (788 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (512 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (116 : ℝ) * a^4 * (c - b)^4 + (330 : ℝ) * a^3 * (b - a)^5 + (672 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (872 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (756 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (334 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (54 : ℝ) * a^3 * (c - b)^5 + (149 : ℝ) * a^2 * (b - a)^6 + (354 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (515 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (552 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (362 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (120 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (15 : ℝ) * a^2 * (c - b)^6 + (34 : ℝ) * a^1 * (b - a)^7 + (92 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (152 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (198 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (174 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (88 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (22 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2 : ℝ) * a^1 * (c - b)^7 + (3 : ℝ) * (b - a)^8 + (9 : ℝ) * (b - a)^7 * (c - b)^1 + (17 : ℝ) * (b - a)^6 * (c - b)^2 + (27 : ℝ) * (b - a)^5 * (c - b)^3 + (30 : ℝ) * (b - a)^4 * (c - b)^4 + (20 : ℝ) * (b - a)^3 * (c - b)^5 + (7 : ℝ) * (b - a)^2 * (c - b)^6 + (1 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^7*b + a^7*c + a^6*b*c + 2*a^5*b^3 + 4*a^5*b^2*c + a^5*b*c^2 - a^5*c^3 + 2*a^4*b^3*c - a^4*b*c^3 - a^3*b^5 - a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 + 2*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^5*c - 10*a^2*b^3*c^3 + 4*a^2*b*c^5 + a*b^7 + a*b^6*c + 4*a*b^5*c^2 + 2*a*b^4*c^3 - a*b^3*c^4 + a*b^2*c^5 + a*b*c^6 + a*c^7 + b^7*c + 2*b^5*c^3 - b^3*c^5 + b*c^7) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * a^6 * (c - a)^2 + (64 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (64 : ℝ) * a^6 * (b - c)^2 + (248 : ℝ) * a^5 * (c - a)^3 + (408 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (432 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (136 : ℝ) * a^5 * (b - c)^3 + (396 : ℝ) * a^4 * (c - a)^4 + (912 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (1148 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (632 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (116 : ℝ) * a^4 * (b - c)^4 + (330 : ℝ) * a^3 * (c - a)^5 + (978 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (1484 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (1128 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (400 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (54 : ℝ) * a^3 * (b - c)^5 + (149 : ℝ) * a^2 * (c - a)^6 + (540 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (980 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (948 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (491 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (132 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (15 : ℝ) * a^2 * (b - c)^6 + (34 : ℝ) * a^1 * (c - a)^7 + (146 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (314 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (372 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (252 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (100 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (22 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (2 : ℝ) * a^1 * (b - c)^7 + (3 : ℝ) * (c - a)^8 + (15 : ℝ) * (c - a)^7 * (b - c)^1 + (38 : ℝ) * (c - a)^6 * (b - c)^2 + (54 : ℝ) * (c - a)^5 * (b - c)^3 + (45 : ℝ) * (c - a)^4 * (b - c)^4 + (23 : ℝ) * (c - a)^3 * (b - c)^5 + (7 : ℝ) * (c - a)^2 * (b - c)^6 + (1 : ℝ) * (c - a)^1 * (b - c)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7*b + a^7*c + a^6*b*c + 2*a^5*b^3 + 4*a^5*b^2*c + a^5*b*c^2 - a^5*c^3 + 2*a^4*b^3*c - a^4*b*c^3 - a^3*b^5 - a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 + 2*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^5*c - 10*a^2*b^3*c^3 + 4*a^2*b*c^5 + a*b^7 + a*b^6*c + 4*a*b^5*c^2 + 2*a*b^4*c^3 - a*b^3*c^4 + a*b^2*c^5 + a*b*c^6 + a*c^7 + b^7*c + 2*b^5*c^3 - b^3*c^5 + b*c^7) := by
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
  have hn : 0 ≤ (a^7*b + a^7*c + a^6*b*c + 2*a^5*b^3 + 4*a^5*b^2*c + a^5*b*c^2 - a^5*c^3 + 2*a^4*b^3*c - a^4*b*c^3 - a^3*b^5 - a^3*b^4*c - 10*a^3*b^3*c^2 - 10*a^3*b^2*c^3 + 2*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^5*c - 10*a^2*b^3*c^3 + 4*a^2*b*c^5 + a*b^7 + a*b^6*c + 4*a*b^5*c^2 + 2*a*b^4*c^3 - a*b^3*c^4 + a*b^2*c^5 + a*b*c^6 + a*c^7 + b^7*c + 2*b^5*c^3 - b^3*c^5 + b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + 3 * b^2) / (b + c)^2 + (b^2 + 3 * c^2) / (c + a)^2 + (c^2 + 3 * a^2) / (a + b)^2 - 1 ≥ 2 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a)) := @solution
#print axioms solution
