-- Prove2me | solution 1 for WorkbookSource.base_6322
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:19:09.614285+00:00
-- url     : https://prove2.me/submissions/d555e310-7e30-4e11-b298-d06d926673ca

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a ^ 2 + b ^ 2) / (2 * a ^ 2 + a * b + b ^ 2) + b * (b ^ 2 + c ^ 2) / (2 * b ^ 2 + b * c + c ^ 2) + c * (c ^ 2 + a ^ 2) / (2 * c ^ 2 + c * a + a ^ 2)) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) / (2 * (a + b + c))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^6*b^2 + 4*a^6*b*c + 4*a^6*c^2 - 2*a^5*b^3 - 3*a^5*b^2*c - 5*a^5*b*c^2 - 2*a^5*c^3 + 8*a^4*b^4 - 11*a^4*b^3*c + 12*a^4*b^2*c^2 - 5*a^4*b*c^3 + 8*a^4*c^4 - 2*a^3*b^5 - 5*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 - 11*a^3*b*c^4 - 2*a^3*c^5 + 4*a^2*b^6 - 5*a^2*b^5*c + 12*a^2*b^4*c^2 - 8*a^2*b^3*c^3 + 12*a^2*b^2*c^4 - 3*a^2*b*c^5 + 8*a^2*c^6 + 4*a*b^6*c - 3*a*b^5*c^2 - 11*a*b^4*c^3 - 5*a*b^3*c^4 - 5*a*b^2*c^5 + 4*a*b*c^6 + 8*b^6*c^2 - 2*b^5*c^3 + 8*b^4*c^4 - 2*b^3*c^5 + 4*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (104 : ℝ) * a^6 * (b - a)^2 + (104 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (104 : ℝ) * a^6 * (c - b)^2 + (412 : ℝ) * a^5 * (b - a)^3 + (573 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (585 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (212 : ℝ) * a^5 * (c - b)^3 + (692 : ℝ) * a^4 * (b - a)^4 + (1234 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1381 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (839 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (192 : ℝ) * a^4 * (c - b)^4 + (644 : ℝ) * a^3 * (b - a)^5 + (1401 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1722 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1332 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (535 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (84 : ℝ) * a^3 * (c - b)^5 + (356 : ℝ) * a^2 * (b - a)^6 + (916 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1220 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1066 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (555 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (149 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (16 : ℝ) * a^2 * (c - b)^6 + (112 : ℝ) * a^1 * (b - a)^7 + (336 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (484 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (449 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (262 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (85 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (12 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (16 : ℝ) * (b - a)^8 + (56 : ℝ) * (b - a)^7 * (c - b)^1 + (90 : ℝ) * (b - a)^6 * (c - b)^2 + (90 : ℝ) * (b - a)^5 * (c - b)^3 + (58 : ℝ) * (b - a)^4 * (c - b)^4 + (22 : ℝ) * (b - a)^3 * (c - b)^5 + (4 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (8*a^6*b^2 + 4*a^6*b*c + 4*a^6*c^2 - 2*a^5*b^3 - 3*a^5*b^2*c - 5*a^5*b*c^2 - 2*a^5*c^3 + 8*a^4*b^4 - 11*a^4*b^3*c + 12*a^4*b^2*c^2 - 5*a^4*b*c^3 + 8*a^4*c^4 - 2*a^3*b^5 - 5*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 - 11*a^3*b*c^4 - 2*a^3*c^5 + 4*a^2*b^6 - 5*a^2*b^5*c + 12*a^2*b^4*c^2 - 8*a^2*b^3*c^3 + 12*a^2*b^2*c^4 - 3*a^2*b*c^5 + 8*a^2*c^6 + 4*a*b^6*c - 3*a*b^5*c^2 - 11*a*b^4*c^3 - 5*a*b^3*c^4 - 5*a*b^2*c^5 + 4*a*b*c^6 + 8*b^6*c^2 - 2*b^5*c^3 + 8*b^4*c^4 - 2*b^3*c^5 + 4*b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (104 : ℝ) * a^6 * (c - a)^2 + (104 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (104 : ℝ) * a^6 * (b - c)^2 + (412 : ℝ) * a^5 * (c - a)^3 + (663 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (675 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (212 : ℝ) * a^5 * (b - c)^3 + (692 : ℝ) * a^4 * (c - a)^4 + (1534 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (1831 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (989 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (192 : ℝ) * a^4 * (b - c)^4 + (644 : ℝ) * a^3 * (c - a)^5 + (1819 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (2558 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (1868 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (653 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (84 : ℝ) * a^3 * (b - c)^5 + (356 : ℝ) * a^2 * (c - a)^6 + (1220 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (1980 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (1774 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (857 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (199 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (16 : ℝ) * a^2 * (b - c)^6 + (112 : ℝ) * a^1 * (c - a)^7 + (448 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (820 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (851 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (506 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (159 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (20 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (16 : ℝ) * (c - a)^8 + (72 : ℝ) * (c - a)^7 * (b - c)^1 + (146 : ℝ) * (c - a)^6 * (b - c)^2 + (170 : ℝ) * (c - a)^5 * (b - c)^3 + (118 : ℝ) * (c - a)^4 * (b - c)^4 + (46 : ℝ) * (c - a)^3 * (b - c)^5 + (8 : ℝ) * (c - a)^2 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^6*b^2 + 4*a^6*b*c + 4*a^6*c^2 - 2*a^5*b^3 - 3*a^5*b^2*c - 5*a^5*b*c^2 - 2*a^5*c^3 + 8*a^4*b^4 - 11*a^4*b^3*c + 12*a^4*b^2*c^2 - 5*a^4*b*c^3 + 8*a^4*c^4 - 2*a^3*b^5 - 5*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 - 11*a^3*b*c^4 - 2*a^3*c^5 + 4*a^2*b^6 - 5*a^2*b^5*c + 12*a^2*b^4*c^2 - 8*a^2*b^3*c^3 + 12*a^2*b^2*c^4 - 3*a^2*b*c^5 + 8*a^2*c^6 + 4*a*b^6*c - 3*a*b^5*c^2 - 11*a*b^4*c^3 - 5*a*b^3*c^4 - 5*a*b^2*c^5 + 4*a*b*c^6 + 8*b^6*c^2 - 2*b^5*c^3 + 8*b^4*c^4 - 2*b^3*c^5 + 4*b^2*c^6) := by
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
  have hn : 0 ≤ (8*a^6*b^2 + 4*a^6*b*c + 4*a^6*c^2 - 2*a^5*b^3 - 3*a^5*b^2*c - 5*a^5*b*c^2 - 2*a^5*c^3 + 8*a^4*b^4 - 11*a^4*b^3*c + 12*a^4*b^2*c^2 - 5*a^4*b*c^3 + 8*a^4*c^4 - 2*a^3*b^5 - 5*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 - 11*a^3*b*c^4 - 2*a^3*c^5 + 4*a^2*b^6 - 5*a^2*b^5*c + 12*a^2*b^4*c^2 - 8*a^2*b^3*c^3 + 12*a^2*b^2*c^4 - 3*a^2*b*c^5 + 8*a^2*c^6 + 4*a*b^6*c - 3*a*b^5*c^2 - 11*a*b^4*c^3 - 5*a*b^3*c^4 - 5*a*b^2*c^5 + 4*a*b*c^6 + 8*b^6*c^2 - 2*b^5*c^3 + 8*b^4*c^4 - 2*b^3*c^5 + 4*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (a ^ 2 + b ^ 2) / (2 * a ^ 2 + a * b + b ^ 2) + b * (b ^ 2 + c ^ 2) / (2 * b ^ 2 + b * c + c ^ 2) + c * (c ^ 2 + a ^ 2) / (2 * c ^ 2 + c * a + a ^ 2)) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) / (2 * (a + b + c))) := @solution
#print axioms solution
