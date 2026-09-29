-- Prove2me | solution 1 for WorkbookSource.base_53584
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:09:00.479113+00:00
-- url     : https://prove2.me/submissions/2215e7df-a9a6-4f3d-a6e5-198b8879a461

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a ^ 2 + b ^ 2) / (5 * a ^ 2 + 3 * b ^ 2) + b * (b ^ 2 + c ^ 2) / (5 * b ^ 2 + 3 * c ^ 2) + c * (c ^ 2 + a ^ 2) / (5 * c ^ 2 + 3 * a ^ 2)) ≥ 3 / 4 * (a * b + b * c + c * a) / (a + b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (60*a^6*b^2 + 36*a^6*c^2 - 105*a^5*b^3 - 65*a^5*b^2*c - 39*a^5*b*c^2 - 39*a^5*c^3 + 120*a^4*b^4 - 65*a^4*b^3*c + 296*a^4*b^2*c^2 - 15*a^4*b*c^3 + 120*a^4*c^4 - 39*a^3*b^5 - 15*a^3*b^4*c - 184*a^3*b^3*c^2 - 184*a^3*b^2*c^3 - 65*a^3*b*c^4 - 105*a^3*c^5 + 36*a^2*b^6 - 39*a^2*b^5*c + 296*a^2*b^4*c^2 - 184*a^2*b^3*c^3 + 296*a^2*b^2*c^4 - 65*a^2*b*c^5 + 60*a^2*c^6 - 65*a*b^5*c^2 - 65*a*b^4*c^3 - 15*a*b^3*c^4 - 39*a*b^2*c^5 + 60*b^6*c^2 - 105*b^5*c^3 + 120*b^4*c^4 - 39*b^3*c^5 + 36*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (320 : ℝ) * a^6 * (b - a)^2 + (320 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (320 : ℝ) * a^6 * (c - b)^2 + (1248 : ℝ) * a^5 * (b - a)^3 + (2232 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (2328 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (672 : ℝ) * a^5 * (c - b)^3 + (2096 : ℝ) * a^4 * (b - a)^4 + (5392 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (6888 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (3592 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (656 : ℝ) * a^4 * (c - b)^4 + (1976 : ℝ) * a^3 * (b - a)^5 + (6390 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (9804 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (7116 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (2382 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (328 : ℝ) * a^3 * (c - b)^5 + (1128 : ℝ) * a^2 * (b - a)^6 + (4166 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (7295 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (6540 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (3031 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (748 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (96 : ℝ) * a^2 * (c - b)^6 + (392 : ℝ) * a^1 * (b - a)^7 + (1562 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (2950 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (3010 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (1650 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (492 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (72 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (72 : ℝ) * (b - a)^8 + (306 : ℝ) * (b - a)^7 * (c - b)^1 + (615 : ℝ) * (b - a)^6 * (c - b)^2 + (705 : ℝ) * (b - a)^5 * (c - b)^3 + (465 : ℝ) * (b - a)^4 * (c - b)^4 + (177 : ℝ) * (b - a)^3 * (c - b)^5 + (36 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (60*a^6*b^2 + 36*a^6*c^2 - 105*a^5*b^3 - 65*a^5*b^2*c - 39*a^5*b*c^2 - 39*a^5*c^3 + 120*a^4*b^4 - 65*a^4*b^3*c + 296*a^4*b^2*c^2 - 15*a^4*b*c^3 + 120*a^4*c^4 - 39*a^3*b^5 - 15*a^3*b^4*c - 184*a^3*b^3*c^2 - 184*a^3*b^2*c^3 - 65*a^3*b*c^4 - 105*a^3*c^5 + 36*a^2*b^6 - 39*a^2*b^5*c + 296*a^2*b^4*c^2 - 184*a^2*b^3*c^3 + 296*a^2*b^2*c^4 - 65*a^2*b*c^5 + 60*a^2*c^6 - 65*a*b^5*c^2 - 65*a*b^4*c^3 - 15*a*b^3*c^4 - 39*a*b^2*c^5 + 60*b^6*c^2 - 105*b^5*c^3 + 120*b^4*c^4 - 39*b^3*c^5 + 36*b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (320 : ℝ) * a^6 * (c - a)^2 + (320 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (320 : ℝ) * a^6 * (b - c)^2 + (1248 : ℝ) * a^5 * (c - a)^3 + (1512 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (1608 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (672 : ℝ) * a^5 * (b - c)^3 + (2096 : ℝ) * a^4 * (c - a)^4 + (2992 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (3288 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (2392 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (656 : ℝ) * a^4 * (b - c)^4 + (1976 : ℝ) * a^3 * (c - a)^5 + (3490 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (4004 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (3716 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (1882 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (328 : ℝ) * a^3 * (b - c)^5 + (1128 : ℝ) * a^2 * (c - a)^6 + (2602 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (3385 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (3540 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (2441 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (812 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (96 : ℝ) * a^2 * (b - c)^6 + (392 : ℝ) * a^1 * (c - a)^7 + (1182 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (1810 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (2030 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (1590 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (700 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (120 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (72 : ℝ) * (c - a)^8 + (270 : ℝ) * (c - a)^7 * (b - c)^1 + (489 : ℝ) * (c - a)^6 * (b - c)^2 + (591 : ℝ) * (c - a)^5 * (b - c)^3 + (495 : ℝ) * (c - a)^4 * (b - c)^4 + (255 : ℝ) * (c - a)^3 * (b - c)^5 + (60 : ℝ) * (c - a)^2 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (60*a^6*b^2 + 36*a^6*c^2 - 105*a^5*b^3 - 65*a^5*b^2*c - 39*a^5*b*c^2 - 39*a^5*c^3 + 120*a^4*b^4 - 65*a^4*b^3*c + 296*a^4*b^2*c^2 - 15*a^4*b*c^3 + 120*a^4*c^4 - 39*a^3*b^5 - 15*a^3*b^4*c - 184*a^3*b^3*c^2 - 184*a^3*b^2*c^3 - 65*a^3*b*c^4 - 105*a^3*c^5 + 36*a^2*b^6 - 39*a^2*b^5*c + 296*a^2*b^4*c^2 - 184*a^2*b^3*c^3 + 296*a^2*b^2*c^4 - 65*a^2*b*c^5 + 60*a^2*c^6 - 65*a*b^5*c^2 - 65*a*b^4*c^3 - 15*a*b^3*c^4 - 39*a*b^2*c^5 + 60*b^6*c^2 - 105*b^5*c^3 + 120*b^4*c^4 - 39*b^3*c^5 + 36*b^2*c^6) := by
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
  have hn : 0 ≤ (60*a^6*b^2 + 36*a^6*c^2 - 105*a^5*b^3 - 65*a^5*b^2*c - 39*a^5*b*c^2 - 39*a^5*c^3 + 120*a^4*b^4 - 65*a^4*b^3*c + 296*a^4*b^2*c^2 - 15*a^4*b*c^3 + 120*a^4*c^4 - 39*a^3*b^5 - 15*a^3*b^4*c - 184*a^3*b^3*c^2 - 184*a^3*b^2*c^3 - 65*a^3*b*c^4 - 105*a^3*c^5 + 36*a^2*b^6 - 39*a^2*b^5*c + 296*a^2*b^4*c^2 - 184*a^2*b^3*c^3 + 296*a^2*b^2*c^4 - 65*a^2*b*c^5 + 60*a^2*c^6 - 65*a*b^5*c^2 - 65*a*b^4*c^3 - 15*a*b^3*c^4 - 39*a*b^2*c^5 + 60*b^6*c^2 - 105*b^5*c^3 + 120*b^4*c^4 - 39*b^3*c^5 + 36*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (a ^ 2 + b ^ 2) / (5 * a ^ 2 + 3 * b ^ 2) + b * (b ^ 2 + c ^ 2) / (5 * b ^ 2 + 3 * c ^ 2) + c * (c ^ 2 + a ^ 2) / (5 * c ^ 2 + 3 * a ^ 2)) ≥ 3 / 4 * (a * b + b * c + c * a) / (a + b + c)) := @solution
#print axioms solution
