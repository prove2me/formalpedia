-- Prove2me | solution 1 for WorkbookSource.base_11458
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:39:35.666772+00:00
-- url     : https://prove2.me/submissions/a45934ba-91e8-47d7-923d-770157e9307d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (3 * a + b + c) / (b ^ 2 + c ^ 2) + b * (3 * b + c + a) / (c ^ 2 + a ^ 2) + c * (3 * c + a + b) / (a ^ 2 + b ^ 2) + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 17 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^8 + 2*a^7*b + 2*a^7*c - 5*a^6*b^2 - 5*a^6*c^2 + 8*a^5*b^3 + 8*a^5*b^2*c + 8*a^5*b*c^2 + 8*a^5*c^3 - 22*a^4*b^4 + 6*a^4*b^3*c - 38*a^4*b^2*c^2 + 6*a^4*b*c^3 - 22*a^4*c^4 + 8*a^3*b^5 + 6*a^3*b^4*c + 16*a^3*b^3*c^2 + 16*a^3*b^2*c^3 + 6*a^3*b*c^4 + 8*a^3*c^5 - 5*a^2*b^6 + 8*a^2*b^5*c - 38*a^2*b^4*c^2 + 16*a^2*b^3*c^3 - 38*a^2*b^2*c^4 + 8*a^2*b*c^5 - 5*a^2*c^6 + 2*a*b^7 + 8*a*b^5*c^2 + 6*a*b^4*c^3 + 6*a*b^3*c^4 + 8*a*b^2*c^5 + 2*a*c^7 + 6*b^8 + 2*b^7*c - 5*b^6*c^2 + 8*b^5*c^3 - 22*b^4*c^4 + 8*b^3*c^5 - 5*b^2*c^6 + 2*b*c^7 + 6*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (128 : ℝ) * a^6 * (b - a)^2 + (128 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (128 : ℝ) * a^6 * (c - b)^2 + (392 : ℝ) * a^5 * (b - a)^3 + (588 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (948 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (376 : ℝ) * a^5 * (c - b)^3 + (540 : ℝ) * a^4 * (b - a)^4 + (1080 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (2480 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (1940 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (500 : ℝ) * a^4 * (c - b)^4 + (408 : ℝ) * a^3 * (b - a)^5 + (1020 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (3208 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (3792 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (1980 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (392 : ℝ) * a^3 * (c - b)^5 + (170 : ℝ) * a^2 * (b - a)^6 + (510 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (2237 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (3624 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (2873 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (1146 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (186 : ℝ) * a^2 * (c - b)^6 + (32 : ℝ) * a^1 * (b - a)^7 + (112 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (796 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (1710 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (1848 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (1118 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (368 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (52 : ℝ) * a^1 * (c - b)^7 + (102 : ℝ) * (b - a)^6 * (c - b)^2 + (306 : ℝ) * (b - a)^5 * (c - b)^3 + (433 : ℝ) * (b - a)^4 * (c - b)^4 + (356 : ℝ) * (b - a)^3 * (c - b)^5 + (177 : ℝ) * (b - a)^2 * (c - b)^6 + (50 : ℝ) * (b - a)^1 * (c - b)^7 + (6 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^8 + 2*a^7*b + 2*a^7*c - 5*a^6*b^2 - 5*a^6*c^2 + 8*a^5*b^3 + 8*a^5*b^2*c + 8*a^5*b*c^2 + 8*a^5*c^3 - 22*a^4*b^4 + 6*a^4*b^3*c - 38*a^4*b^2*c^2 + 6*a^4*b*c^3 - 22*a^4*c^4 + 8*a^3*b^5 + 6*a^3*b^4*c + 16*a^3*b^3*c^2 + 16*a^3*b^2*c^3 + 6*a^3*b*c^4 + 8*a^3*c^5 - 5*a^2*b^6 + 8*a^2*b^5*c - 38*a^2*b^4*c^2 + 16*a^2*b^3*c^3 - 38*a^2*b^2*c^4 + 8*a^2*b*c^5 - 5*a^2*c^6 + 2*a*b^7 + 8*a*b^5*c^2 + 6*a*b^4*c^3 + 6*a*b^3*c^4 + 8*a*b^2*c^5 + 2*a*c^7 + 6*b^8 + 2*b^7*c - 5*b^6*c^2 + 8*b^5*c^3 - 22*b^4*c^4 + 8*b^3*c^5 - 5*b^2*c^6 + 2*b*c^7 + 6*c^8) := by
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
  have hn : 0 ≤ (6*a^8 + 2*a^7*b + 2*a^7*c - 5*a^6*b^2 - 5*a^6*c^2 + 8*a^5*b^3 + 8*a^5*b^2*c + 8*a^5*b*c^2 + 8*a^5*c^3 - 22*a^4*b^4 + 6*a^4*b^3*c - 38*a^4*b^2*c^2 + 6*a^4*b*c^3 - 22*a^4*c^4 + 8*a^3*b^5 + 6*a^3*b^4*c + 16*a^3*b^3*c^2 + 16*a^3*b^2*c^3 + 6*a^3*b*c^4 + 8*a^3*c^5 - 5*a^2*b^6 + 8*a^2*b^5*c - 38*a^2*b^4*c^2 + 16*a^2*b^3*c^3 - 38*a^2*b^2*c^4 + 8*a^2*b*c^5 - 5*a^2*c^6 + 2*a*b^7 + 8*a*b^5*c^2 + 6*a*b^4*c^3 + 6*a*b^3*c^4 + 8*a*b^2*c^5 + 2*a*c^7 + 6*b^8 + 2*b^7*c - 5*b^6*c^2 + 8*b^5*c^3 - 22*b^4*c^4 + 8*b^3*c^5 - 5*b^2*c^6 + 2*b*c^7 + 6*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (3 * a + b + c) / (b ^ 2 + c ^ 2) + b * (3 * b + c + a) / (c ^ 2 + a ^ 2) + c * (3 * c + a + b) / (a ^ 2 + b ^ 2) + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 17 / 2) := @solution
#print axioms solution
