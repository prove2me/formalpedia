-- Prove2me | solution 1 for WorkbookSource.plus_1420
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:39.206528+00:00
-- url     : https://prove2.me/submissions/01162589-043c-4835-a75f-2448b2a5ae99

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + b)) ^ 2 + (b / (b + c)) ^ 2 + (c / (c + a)) ^ 2 ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) / (4 * (a * b + b * c + a * c))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 - 2*a^5*b^3 + 2*a^5*b^2*c + 6*a^5*b*c^2 + 2*a^5*c^3 - 2*a^4*b^4 - 8*a^4*b^3*c - 4*a^4*b^2*c^2 - 4*a^4*b*c^3 - 2*a^4*c^4 + 2*a^3*b^5 - 4*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 8*a^3*b*c^4 - 2*a^3*c^5 + 3*a^2*b^6 + 6*a^2*b^5*c - 4*a^2*b^4*c^2 - 2*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 2*a^2*b*c^5 + 3*a^2*c^6 + 6*a*b^6*c + 2*a*b^5*c^2 - 8*a*b^4*c^3 - 4*a*b^3*c^4 + 6*a*b^2*c^5 + 6*a*b*c^6 + 3*b^6*c^2 - 2*b^5*c^3 - 2*b^4*c^4 + 2*b^3*c^5 + 3*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^6 * (b - a)^2 + (96 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^6 * (c - b)^2 + (352 : ℝ) * a^5 * (b - a)^3 + (576 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (672 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (224 : ℝ) * a^5 * (c - b)^3 + (520 : ℝ) * a^4 * (b - a)^4 + (1200 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1720 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (1040 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (200 : ℝ) * a^4 * (c - b)^4 + (400 : ℝ) * a^3 * (b - a)^5 + (1204 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (2088 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1768 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (644 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (80 : ℝ) * a^3 * (c - b)^5 + (172 : ℝ) * a^2 * (b - a)^6 + (640 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1301 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1386 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (717 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (164 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (12 : ℝ) * a^2 * (c - b)^6 + (40 : ℝ) * a^1 * (b - a)^7 + (176 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (404 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (506 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (328 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (102 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (12 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * (b - a)^8 + (20 : ℝ) * (b - a)^7 * (c - b)^1 + (50 : ℝ) * (b - a)^6 * (c - b)^2 + (70 : ℝ) * (b - a)^5 * (c - b)^3 + (53 : ℝ) * (b - a)^4 * (c - b)^4 + (20 : ℝ) * (b - a)^3 * (c - b)^5 + (3 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 - 2*a^5*b^3 + 2*a^5*b^2*c + 6*a^5*b*c^2 + 2*a^5*c^3 - 2*a^4*b^4 - 8*a^4*b^3*c - 4*a^4*b^2*c^2 - 4*a^4*b*c^3 - 2*a^4*c^4 + 2*a^3*b^5 - 4*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 8*a^3*b*c^4 - 2*a^3*c^5 + 3*a^2*b^6 + 6*a^2*b^5*c - 4*a^2*b^4*c^2 - 2*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 2*a^2*b*c^5 + 3*a^2*c^6 + 6*a*b^6*c + 2*a*b^5*c^2 - 8*a*b^4*c^3 - 4*a*b^3*c^4 + 6*a*b^2*c^5 + 6*a*b*c^6 + 3*b^6*c^2 - 2*b^5*c^3 - 2*b^4*c^4 + 2*b^3*c^5 + 3*b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^6 * (c - a)^2 + (96 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (96 : ℝ) * a^6 * (b - c)^2 + (352 : ℝ) * a^5 * (c - a)^3 + (480 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (576 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (224 : ℝ) * a^5 * (b - c)^3 + (520 : ℝ) * a^4 * (c - a)^4 + (880 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (1240 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (880 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (200 : ℝ) * a^4 * (b - c)^4 + (400 : ℝ) * a^3 * (c - a)^5 + (796 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (1272 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (1272 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (556 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (80 : ℝ) * a^3 * (b - c)^5 + (172 : ℝ) * a^2 * (c - a)^6 + (392 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (681 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (858 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (545 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (148 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (12 : ℝ) * a^2 * (b - c)^6 + (40 : ℝ) * a^1 * (c - a)^7 + (104 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (188 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (274 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (224 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (86 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (12 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (4 : ℝ) * (c - a)^8 + (12 : ℝ) * (c - a)^7 * (b - c)^1 + (22 : ℝ) * (c - a)^6 * (b - c)^2 + (34 : ℝ) * (c - a)^5 * (b - c)^3 + (33 : ℝ) * (c - a)^4 * (b - c)^4 + (16 : ℝ) * (c - a)^3 * (b - c)^5 + (3 : ℝ) * (c - a)^2 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 - 2*a^5*b^3 + 2*a^5*b^2*c + 6*a^5*b*c^2 + 2*a^5*c^3 - 2*a^4*b^4 - 8*a^4*b^3*c - 4*a^4*b^2*c^2 - 4*a^4*b*c^3 - 2*a^4*c^4 + 2*a^3*b^5 - 4*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 8*a^3*b*c^4 - 2*a^3*c^5 + 3*a^2*b^6 + 6*a^2*b^5*c - 4*a^2*b^4*c^2 - 2*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 2*a^2*b*c^5 + 3*a^2*c^6 + 6*a*b^6*c + 2*a*b^5*c^2 - 8*a*b^4*c^3 - 4*a*b^3*c^4 + 6*a*b^2*c^5 + 6*a*b*c^6 + 3*b^6*c^2 - 2*b^5*c^3 - 2*b^4*c^4 + 2*b^3*c^5 + 3*b^2*c^6) := by
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
  have hn : 0 ≤ (3*a^6*b^2 + 6*a^6*b*c + 3*a^6*c^2 - 2*a^5*b^3 + 2*a^5*b^2*c + 6*a^5*b*c^2 + 2*a^5*c^3 - 2*a^4*b^4 - 8*a^4*b^3*c - 4*a^4*b^2*c^2 - 4*a^4*b*c^3 - 2*a^4*c^4 + 2*a^3*b^5 - 4*a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - 8*a^3*b*c^4 - 2*a^3*c^5 + 3*a^2*b^6 + 6*a^2*b^5*c - 4*a^2*b^4*c^2 - 2*a^2*b^3*c^3 - 4*a^2*b^2*c^4 + 2*a^2*b*c^5 + 3*a^2*c^6 + 6*a*b^6*c + 2*a*b^5*c^2 - 8*a*b^4*c^3 - 4*a*b^3*c^4 + 6*a*b^2*c^5 + 6*a*b*c^6 + 3*b^6*c^2 - 2*b^5*c^3 - 2*b^4*c^4 + 2*b^3*c^5 + 3*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (a + b)) ^ 2 + (b / (b + c)) ^ 2 + (c / (c + a)) ^ 2 ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) / (4 * (a * b + b * c + a * c))) := @solution
#print axioms solution
