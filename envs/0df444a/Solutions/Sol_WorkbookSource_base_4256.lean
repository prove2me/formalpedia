-- Prove2me | solution 1 for WorkbookSource.base_4256
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:12.099731+00:00
-- url     : https://prove2.me/submissions/cba89626-ddcf-4300-99c9-23b35c00d895

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (3 * a^2 + (b + c)^2) + b^2 / (3 * b^2 + (c + a)^2) + c^2 / (3 * c^2 + (a + b)^2)) ≤ (3 * (a^2 + b^2 + c^2)) / (7 * (a * b + b * c + c * a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (9*a^8 + 11*a^7*b + 11*a^7*c + 34*a^6*b^2 + 7*a^6*b*c + 34*a^6*c^2 + 29*a^5*b^3 - 37*a^5*b^2*c - 37*a^5*b*c^2 + 29*a^5*c^3 - 6*a^4*b^4 - 69*a^4*b^3*c + 160*a^4*b^2*c^2 - 69*a^4*b*c^3 - 6*a^4*c^4 + 29*a^3*b^5 - 69*a^3*b^4*c - 106*a^3*b^3*c^2 - 106*a^3*b^2*c^3 - 69*a^3*b*c^4 + 29*a^3*c^5 + 34*a^2*b^6 - 37*a^2*b^5*c + 160*a^2*b^4*c^2 - 106*a^2*b^3*c^3 + 160*a^2*b^2*c^4 - 37*a^2*b*c^5 + 34*a^2*c^6 + 11*a*b^7 + 7*a*b^6*c - 37*a*b^5*c^2 - 69*a*b^4*c^3 - 69*a*b^3*c^4 - 37*a*b^2*c^5 + 7*a*b*c^6 + 11*a*c^7 + 9*b^8 + 11*b^7*c + 34*b^6*c^2 + 29*b^5*c^3 - 6*b^4*c^4 + 29*b^3*c^5 + 34*b^2*c^6 + 11*b*c^7 + 9*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1071 : ℝ) * a^6 * (b - a)^2 + (1071 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (1071 : ℝ) * a^6 * (c - b)^2 + (4064 : ℝ) * a^5 * (b - a)^3 + (6096 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (6756 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (2362 : ℝ) * a^5 * (c - b)^3 + (6710 : ℝ) * a^4 * (b - a)^4 + (13420 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (17525 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (10815 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (2455 : ℝ) * a^4 * (c - b)^4 + (6220 : ℝ) * a^3 * (b - a)^5 + (15550 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (23660 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (19940 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (8410 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (1400 : ℝ) * a^3 * (c - b)^5 + (3456 : ℝ) * a^2 * (b - a)^6 + (10368 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (18002 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (18724 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (11177 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (3543 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (481 : ℝ) * a^2 * (c - b)^6 + (1104 : ℝ) * a^1 * (b - a)^7 + (3864 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (7516 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (9130 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (6892 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (3140 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (810 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (94 : ℝ) * a^1 * (c - b)^7 + (160 : ℝ) * (b - a)^8 + (640 : ℝ) * (b - a)^7 * (c - b)^1 + (1368 : ℝ) * (b - a)^6 * (c - b)^2 + (1864 : ℝ) * (b - a)^5 * (c - b)^3 + (1664 : ℝ) * (b - a)^4 * (c - b)^4 + (968 : ℝ) * (b - a)^3 * (c - b)^5 + (363 : ℝ) * (b - a)^2 * (c - b)^6 + (83 : ℝ) * (b - a)^1 * (c - b)^7 + (9 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (9*a^8 + 11*a^7*b + 11*a^7*c + 34*a^6*b^2 + 7*a^6*b*c + 34*a^6*c^2 + 29*a^5*b^3 - 37*a^5*b^2*c - 37*a^5*b*c^2 + 29*a^5*c^3 - 6*a^4*b^4 - 69*a^4*b^3*c + 160*a^4*b^2*c^2 - 69*a^4*b*c^3 - 6*a^4*c^4 + 29*a^3*b^5 - 69*a^3*b^4*c - 106*a^3*b^3*c^2 - 106*a^3*b^2*c^3 - 69*a^3*b*c^4 + 29*a^3*c^5 + 34*a^2*b^6 - 37*a^2*b^5*c + 160*a^2*b^4*c^2 - 106*a^2*b^3*c^3 + 160*a^2*b^2*c^4 - 37*a^2*b*c^5 + 34*a^2*c^6 + 11*a*b^7 + 7*a*b^6*c - 37*a*b^5*c^2 - 69*a*b^4*c^3 - 69*a*b^3*c^4 - 37*a*b^2*c^5 + 7*a*b*c^6 + 11*a*c^7 + 9*b^8 + 11*b^7*c + 34*b^6*c^2 + 29*b^5*c^3 - 6*b^4*c^4 + 29*b^3*c^5 + 34*b^2*c^6 + 11*b*c^7 + 9*c^8) := by
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
  have hn : 0 ≤ (9*a^8 + 11*a^7*b + 11*a^7*c + 34*a^6*b^2 + 7*a^6*b*c + 34*a^6*c^2 + 29*a^5*b^3 - 37*a^5*b^2*c - 37*a^5*b*c^2 + 29*a^5*c^3 - 6*a^4*b^4 - 69*a^4*b^3*c + 160*a^4*b^2*c^2 - 69*a^4*b*c^3 - 6*a^4*c^4 + 29*a^3*b^5 - 69*a^3*b^4*c - 106*a^3*b^3*c^2 - 106*a^3*b^2*c^3 - 69*a^3*b*c^4 + 29*a^3*c^5 + 34*a^2*b^6 - 37*a^2*b^5*c + 160*a^2*b^4*c^2 - 106*a^2*b^3*c^3 + 160*a^2*b^2*c^4 - 37*a^2*b*c^5 + 34*a^2*c^6 + 11*a*b^7 + 7*a*b^6*c - 37*a*b^5*c^2 - 69*a*b^4*c^3 - 69*a*b^3*c^4 - 37*a*b^2*c^5 + 7*a*b*c^6 + 11*a*c^7 + 9*b^8 + 11*b^7*c + 34*b^6*c^2 + 29*b^5*c^3 - 6*b^4*c^4 + 29*b^3*c^5 + 34*b^2*c^6 + 11*b*c^7 + 9*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (3 * a^2 + (b + c)^2) + b^2 / (3 * b^2 + (c + a)^2) + c^2 / (3 * c^2 + (a + b)^2)) ≤ (3 * (a^2 + b^2 + c^2)) / (7 * (a * b + b * c + c * a))) := @solution
#print axioms solution
