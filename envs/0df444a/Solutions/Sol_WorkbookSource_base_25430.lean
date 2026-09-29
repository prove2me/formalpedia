-- Prove2me | solution 1 for WorkbookSource.base_25430
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:06:27.116772+00:00
-- url     : https://prove2.me/submissions/14f2afcd-73aa-49bb-8694-039ae0adc473

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b / (4 * a + 7 * b) + b^2 * c / (4 * b + 7 * c) + c^2 * a / (4 * c + 7 * a)) ≥ (5 * (a * b + b * c + c * a) - 2 * (a^2 + b^2 + c^2)) / 33  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (224*a^4*b + 392*a^4*c + 756*a^3*b^2 + 891*a^3*b*c - 756*a^3*c^2 - 756*a^2*b^3 - 1507*a^2*b^2*c - 1507*a^2*b*c^2 + 756*a^2*c^3 + 392*a*b^4 + 891*a*b^3*c - 1507*a*b^2*c^2 + 891*a*b*c^3 + 224*a*c^4 + 224*b^4*c + 756*b^3*c^2 - 756*b^2*c^3 + 392*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3355 : ℝ) * a^3 * (b - a)^2 + (3355 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (3355 : ℝ) * a^3 * (c - b)^2 + (6710 : ℝ) * a^2 * (b - a)^3 + (8301 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (8301 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (3355 : ℝ) * a^2 * (c - b)^3 + (3971 : ℝ) * a^1 * (b - a)^4 + (5590 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (5030 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (3411 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (616 : ℝ) * a^1 * (c - b)^4 + (616 : ℝ) * (b - a)^5 + (1036 : ℝ) * (b - a)^4 * (c - b)^1 + (840 : ℝ) * (b - a)^3 * (c - b)^2 + (812 : ℝ) * (b - a)^2 * (c - b)^3 + (392 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (224*a^4*b + 392*a^4*c + 756*a^3*b^2 + 891*a^3*b*c - 756*a^3*c^2 - 756*a^2*b^3 - 1507*a^2*b^2*c - 1507*a^2*b*c^2 + 756*a^2*c^3 + 392*a*b^4 + 891*a*b^3*c - 1507*a*b^2*c^2 + 891*a*b*c^3 + 224*a*c^4 + 224*b^4*c + 756*b^3*c^2 - 756*b^2*c^3 + 392*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (3355 : ℝ) * a^3 * (c - a)^2 + (3355 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (3355 : ℝ) * a^3 * (b - c)^2 + (6710 : ℝ) * a^2 * (c - a)^3 + (11829 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (11829 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (3355 : ℝ) * a^2 * (b - c)^3 + (3971 : ℝ) * a^1 * (c - a)^4 + (10294 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (12086 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (5763 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (616 : ℝ) * a^1 * (b - c)^4 + (616 : ℝ) * (c - a)^5 + (2044 : ℝ) * (c - a)^4 * (b - c)^1 + (2856 : ℝ) * (c - a)^3 * (b - c)^2 + (1652 : ℝ) * (c - a)^2 * (b - c)^3 + (224 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (224*a^4*b + 392*a^4*c + 756*a^3*b^2 + 891*a^3*b*c - 756*a^3*c^2 - 756*a^2*b^3 - 1507*a^2*b^2*c - 1507*a^2*b*c^2 + 756*a^2*c^3 + 392*a*b^4 + 891*a*b^3*c - 1507*a*b^2*c^2 + 891*a*b*c^3 + 224*a*c^4 + 224*b^4*c + 756*b^3*c^2 - 756*b^2*c^3 + 392*b*c^4) := by
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
  have hn : 0 ≤ (224*a^4*b + 392*a^4*c + 756*a^3*b^2 + 891*a^3*b*c - 756*a^3*c^2 - 756*a^2*b^3 - 1507*a^2*b^2*c - 1507*a^2*b*c^2 + 756*a^2*c^3 + 392*a*b^4 + 891*a*b^3*c - 1507*a*b^2*c^2 + 891*a*b*c^3 + 224*a*c^4 + 224*b^4*c + 756*b^3*c^2 - 756*b^2*c^3 + 392*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 * b / (4 * a + 7 * b) + b^2 * c / (4 * b + 7 * c) + c^2 * a / (4 * c + 7 * a)) ≥ (5 * (a * b + b * c + c * a) - 2 * (a^2 + b^2 + c^2)) / 33) := @solution
#print axioms solution
