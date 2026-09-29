-- Prove2me | solution 1 for WorkbookSource.base_55749
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:30.931699+00:00
-- url     : https://prove2.me/submissions/f202ad77-31c0-416e-aefe-302568ec2340

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 11 * (a^6 + b^6 + c^6) + 40 * a * b * c * (a * b^2 + b * c^2 + c * a^2) ≥ 51 * a * b * c * (a^2 * b + b^2 * c + c^2 * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (11*a^6 - 51*a^3*b^2*c + 40*a^3*b*c^2 + 40*a^2*b^3*c - 51*a^2*b*c^3 - 51*a*b^3*c^2 + 40*a*b^2*c^3 + 11*b^6 + 11*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (121 : ℝ) * a^4 * (b - a)^2 + (121 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (121 : ℝ) * a^4 * (c - b)^2 + (275 : ℝ) * a^3 * (b - a)^3 + (458 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (601 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (209 : ℝ) * a^3 * (c - b)^3 + (264 : ℝ) * a^2 * (b - a)^4 + (619 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1044 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (689 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (165 : ℝ) * a^2 * (c - b)^4 + (121 : ℝ) * a^1 * (b - a)^5 + (348 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (729 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (700 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (330 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (66 : ℝ) * a^1 * (c - b)^5 + (22 : ℝ) * (b - a)^6 + (66 : ℝ) * (b - a)^5 * (c - b)^1 + (165 : ℝ) * (b - a)^4 * (c - b)^2 + (220 : ℝ) * (b - a)^3 * (c - b)^3 + (165 : ℝ) * (b - a)^2 * (c - b)^4 + (66 : ℝ) * (b - a)^1 * (c - b)^5 + (11 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (11*a^6 - 51*a^3*b^2*c + 40*a^3*b*c^2 + 40*a^2*b^3*c - 51*a^2*b*c^3 - 51*a*b^3*c^2 + 40*a*b^2*c^3 + 11*b^6 + 11*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (121 : ℝ) * a^4 * (c - a)^2 + (121 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (121 : ℝ) * a^4 * (b - c)^2 + (275 : ℝ) * a^3 * (c - a)^3 + (367 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (510 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (209 : ℝ) * a^3 * (b - c)^3 + (264 : ℝ) * a^2 * (c - a)^4 + (437 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (771 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (598 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (165 : ℝ) * a^2 * (b - c)^4 + (121 : ℝ) * a^1 * (c - a)^5 + (257 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (547 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (609 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (330 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (66 : ℝ) * a^1 * (b - c)^5 + (22 : ℝ) * (c - a)^6 + (66 : ℝ) * (c - a)^5 * (b - c)^1 + (165 : ℝ) * (c - a)^4 * (b - c)^2 + (220 : ℝ) * (c - a)^3 * (b - c)^3 + (165 : ℝ) * (c - a)^2 * (b - c)^4 + (66 : ℝ) * (c - a)^1 * (b - c)^5 + (11 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (11*a^6 - 51*a^3*b^2*c + 40*a^3*b*c^2 + 40*a^2*b^3*c - 51*a^2*b*c^3 - 51*a*b^3*c^2 + 40*a*b^2*c^3 + 11*b^6 + 11*c^6) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 11 * (a^6 + b^6 + c^6) + 40 * a * b * c * (a * b^2 + b * c^2 + c * a^2) ≥ 51 * a * b * c * (a^2 * b + b^2 * c + c^2 * a)) := @solution
#print axioms solution
