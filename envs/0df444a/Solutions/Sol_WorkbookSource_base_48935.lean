-- Prove2me | solution 1 for WorkbookSource.base_48935
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:11.416108+00:00
-- url     : https://prove2.me/submissions/b3c284ef-e66a-453d-85a0-54cc2259c67c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b) / (4 * b + 4 * c + a) + (b * c) / (4 * a + 4 * c + b) + (a * c) / (4 * b + 4 * a + c) ≥ (a + b + c) * (a * b + b * c + c * a) / (9 * (a ^ 2 + b ^ 2 + c ^ 2))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (128*a^5*b + 20*a^5*c + 80*a^4*b^2 + 153*a^4*b*c + 80*a^4*c^2 + 12*a^3*b^3 - 208*a^3*b^2*c - 100*a^3*b*c^2 + 12*a^3*c^3 + 80*a^2*b^4 - 100*a^2*b^3*c - 495*a^2*b^2*c^2 - 208*a^2*b*c^3 + 80*a^2*c^4 + 20*a*b^5 + 153*a*b^4*c - 208*a*b^3*c^2 - 100*a*b^2*c^3 + 153*a*b*c^4 + 128*a*c^5 + 128*b^5*c + 80*b^4*c^2 + 12*b^3*c^3 + 80*b^2*c^4 + 20*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1863 : ℝ) * a^4 * (b - a)^2 + (1863 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1863 : ℝ) * a^4 * (c - b)^2 + (5004 : ℝ) * a^3 * (b - a)^3 + (7020 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (6912 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (2448 : ℝ) * a^3 * (c - b)^3 + (4887 : ℝ) * a^2 * (b - a)^4 + (8802 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (9207 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (5292 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (1053 : ℝ) * a^2 * (c - b)^4 + (2066 : ℝ) * a^1 * (b - a)^5 + (4409 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (4874 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (3388 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (1153 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (148 : ℝ) * a^1 * (c - b)^5 + (320 : ℝ) * (b - a)^6 + (744 : ℝ) * (b - a)^5 * (c - b)^1 + (796 : ℝ) * (b - a)^4 * (c - b)^2 + (532 : ℝ) * (b - a)^3 * (c - b)^3 + (180 : ℝ) * (b - a)^2 * (c - b)^4 + (20 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (128*a^5*b + 20*a^5*c + 80*a^4*b^2 + 153*a^4*b*c + 80*a^4*c^2 + 12*a^3*b^3 - 208*a^3*b^2*c - 100*a^3*b*c^2 + 12*a^3*c^3 + 80*a^2*b^4 - 100*a^2*b^3*c - 495*a^2*b^2*c^2 - 208*a^2*b*c^3 + 80*a^2*c^4 + 20*a*b^5 + 153*a*b^4*c - 208*a*b^3*c^2 - 100*a*b^2*c^3 + 153*a*b*c^4 + 128*a*c^5 + 128*b^5*c + 80*b^4*c^2 + 12*b^3*c^3 + 80*b^2*c^4 + 20*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (1863 : ℝ) * a^4 * (c - a)^2 + (1863 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (1863 : ℝ) * a^4 * (b - c)^2 + (5004 : ℝ) * a^3 * (c - a)^3 + (7992 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (7884 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (2448 : ℝ) * a^3 * (b - c)^3 + (4887 : ℝ) * a^2 * (c - a)^4 + (10746 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (12123 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (6264 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (1053 : ℝ) * a^2 * (b - c)^4 + (2066 : ℝ) * a^1 * (c - a)^5 + (5921 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (7898 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (5440 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1693 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (148 : ℝ) * a^1 * (b - c)^5 + (320 : ℝ) * (c - a)^6 + (1176 : ℝ) * (c - a)^5 * (b - c)^1 + (1876 : ℝ) * (c - a)^4 * (b - c)^2 + (1612 : ℝ) * (c - a)^3 * (b - c)^3 + (720 : ℝ) * (c - a)^2 * (b - c)^4 + (128 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (128*a^5*b + 20*a^5*c + 80*a^4*b^2 + 153*a^4*b*c + 80*a^4*c^2 + 12*a^3*b^3 - 208*a^3*b^2*c - 100*a^3*b*c^2 + 12*a^3*c^3 + 80*a^2*b^4 - 100*a^2*b^3*c - 495*a^2*b^2*c^2 - 208*a^2*b*c^3 + 80*a^2*c^4 + 20*a*b^5 + 153*a*b^4*c - 208*a*b^3*c^2 - 100*a*b^2*c^3 + 153*a*b*c^4 + 128*a*c^5 + 128*b^5*c + 80*b^4*c^2 + 12*b^3*c^3 + 80*b^2*c^4 + 20*b*c^5) := by
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
  have hn : 0 ≤ ((a + b + c)*(128*a^4*b + 20*a^4*c - 48*a^3*b^2 + 5*a^3*b*c + 60*a^3*c^2 + 60*a^2*b^3 - 165*a^2*b^2*c - 165*a^2*b*c^2 - 48*a^2*c^3 + 20*a*b^4 + 5*a*b^3*c - 165*a*b^2*c^2 + 5*a*b*c^3 + 128*a*c^4 + 128*b^4*c - 48*b^3*c^2 + 60*b^2*c^3 + 20*b*c^4)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b) / (4 * b + 4 * c + a) + (b * c) / (4 * a + 4 * c + b) + (a * c) / (4 * b + 4 * a + c) ≥ (a + b + c) * (a * b + b * c + c * a) / (9 * (a ^ 2 + b ^ 2 + c ^ 2))) := @solution
#print axioms solution
