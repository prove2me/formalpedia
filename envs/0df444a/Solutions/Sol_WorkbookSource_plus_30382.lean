-- Prove2me | solution 1 for WorkbookSource.plus_30382
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:35:40.524986+00:00
-- url     : https://prove2.me/submissions/c9f3617e-aa6a-4b62-8873-cf3a12495a1f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 7 / 4   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^8 + 8*a^7*b + 8*a^7*c + a^6*b^2 + 2*a^6*b*c + a^6*c^2 - 2*a^5*b^3 - 14*a^5*b^2*c - 14*a^5*b*c^2 - 2*a^5*c^3 + 2*a^4*b^4 + 4*a^4*b^3*c - 8*a^4*b^2*c^2 + 4*a^4*b*c^3 + 2*a^4*c^4 - 2*a^3*b^5 + 4*a^3*b^4*c + 6*a^3*b^3*c^2 + 6*a^3*b^2*c^3 + 4*a^3*b*c^4 - 2*a^3*c^5 + a^2*b^6 - 14*a^2*b^5*c - 8*a^2*b^4*c^2 + 6*a^2*b^3*c^3 - 8*a^2*b^2*c^4 - 14*a^2*b*c^5 + a^2*c^6 + 8*a*b^7 + 2*a*b^6*c - 14*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 - 14*a*b^2*c^5 + 2*a*b*c^6 + 8*a*c^7 + 4*b^8 + 8*b^7*c + b^6*c^2 - 2*b^5*c^3 + 2*b^4*c^4 - 2*b^3*c^5 + b^2*c^6 + 8*b*c^7 + 4*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (224 : ℝ) * a^6 * (b - a)^2 + (224 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (224 : ℝ) * a^6 * (c - b)^2 + (768 : ℝ) * a^5 * (b - a)^3 + (1152 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (1536 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (576 : ℝ) * a^5 * (c - b)^3 + (1224 : ℝ) * a^4 * (b - a)^4 + (2448 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (4152 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (2928 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (744 : ℝ) * a^4 * (c - b)^4 + (1144 : ℝ) * a^3 * (b - a)^5 + (2860 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (5816 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (5864 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (2868 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (552 : ℝ) * a^3 * (c - b)^5 + (636 : ℝ) * a^2 * (b - a)^6 + (1908 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (4467 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (5754 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (4071 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (1512 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (228 : ℝ) * a^2 * (c - b)^6 + (192 : ℝ) * a^1 * (b - a)^7 + (672 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (1772 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (2750 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (2512 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (1354 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (396 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (48 : ℝ) * a^1 * (c - b)^7 + (24 : ℝ) * (b - a)^8 + (96 : ℝ) * (b - a)^7 * (c - b)^1 + (282 : ℝ) * (b - a)^6 * (c - b)^2 + (510 : ℝ) * (b - a)^5 * (c - b)^3 + (567 : ℝ) * (b - a)^4 * (c - b)^4 + (396 : ℝ) * (b - a)^3 * (c - b)^5 + (169 : ℝ) * (b - a)^2 * (c - b)^6 + (40 : ℝ) * (b - a)^1 * (c - b)^7 + (4 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^8 + 8*a^7*b + 8*a^7*c + a^6*b^2 + 2*a^6*b*c + a^6*c^2 - 2*a^5*b^3 - 14*a^5*b^2*c - 14*a^5*b*c^2 - 2*a^5*c^3 + 2*a^4*b^4 + 4*a^4*b^3*c - 8*a^4*b^2*c^2 + 4*a^4*b*c^3 + 2*a^4*c^4 - 2*a^3*b^5 + 4*a^3*b^4*c + 6*a^3*b^3*c^2 + 6*a^3*b^2*c^3 + 4*a^3*b*c^4 - 2*a^3*c^5 + a^2*b^6 - 14*a^2*b^5*c - 8*a^2*b^4*c^2 + 6*a^2*b^3*c^3 - 8*a^2*b^2*c^4 - 14*a^2*b*c^5 + a^2*c^6 + 8*a*b^7 + 2*a*b^6*c - 14*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 - 14*a*b^2*c^5 + 2*a*b*c^6 + 8*a*c^7 + 4*b^8 + 8*b^7*c + b^6*c^2 - 2*b^5*c^3 + 2*b^4*c^4 - 2*b^3*c^5 + b^2*c^6 + 8*b*c^7 + 4*c^8) := by
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
  have hn : 0 ≤ (4*a^8 + 8*a^7*b + 8*a^7*c + a^6*b^2 + 2*a^6*b*c + a^6*c^2 - 2*a^5*b^3 - 14*a^5*b^2*c - 14*a^5*b*c^2 - 2*a^5*c^3 + 2*a^4*b^4 + 4*a^4*b^3*c - 8*a^4*b^2*c^2 + 4*a^4*b*c^3 + 2*a^4*c^4 - 2*a^3*b^5 + 4*a^3*b^4*c + 6*a^3*b^3*c^2 + 6*a^3*b^2*c^3 + 4*a^3*b*c^4 - 2*a^3*c^5 + a^2*b^6 - 14*a^2*b^5*c - 8*a^2*b^4*c^2 + 6*a^2*b^3*c^3 - 8*a^2*b^2*c^4 - 14*a^2*b*c^5 + a^2*c^6 + 8*a*b^7 + 2*a*b^6*c - 14*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 - 14*a*b^2*c^5 + 2*a*b*c^6 + 8*a*c^7 + 4*b^8 + 8*b^7*c + b^6*c^2 - 2*b^5*c^3 + 2*b^4*c^4 - 2*b^3*c^5 + b^2*c^6 + 8*b*c^7 + 4*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 7 / 4) := @solution
#print axioms solution
