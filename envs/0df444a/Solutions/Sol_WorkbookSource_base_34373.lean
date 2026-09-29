-- Prove2me | solution 1 for WorkbookSource.base_34373
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:08.864517+00:00
-- url     : https://prove2.me/submissions/ecef8372-78ea-4655-8030-289a8c86e089

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a)) ≥ 4 * (1 / (3 * a + 4 * b + 5 * c) + 1 / (3 * b + 4 * c + 5 * a) + 1 / (3 * c + 4 * a + 5 * b))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (120*a^5 + 426*a^4*b + 54*a^4*c + 315*a^3*b^2 - 120*a^3*b*c - 75*a^3*c^2 - 75*a^2*b^3 - 720*a^2*b^2*c - 720*a^2*b*c^2 + 315*a^2*c^3 + 54*a*b^4 - 120*a*b^3*c - 720*a*b^2*c^2 - 120*a*b*c^3 + 426*a*c^4 + 120*b^5 + 426*b^4*c + 315*b^3*c^2 - 75*b^2*c^3 + 54*b*c^4 + 120*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3240 : ℝ) * a^3 * (b - a)^2 + (3240 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (3240 : ℝ) * a^3 * (c - b)^2 + (6480 : ℝ) * a^2 * (b - a)^3 + (8019 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (8019 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (3240 : ℝ) * a^2 * (c - b)^3 + (4320 : ℝ) * a^1 * (b - a)^4 + (6372 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (6318 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (4266 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (1080 : ℝ) * a^1 * (c - b)^4 + (960 : ℝ) * (b - a)^5 + (1647 : ℝ) * (b - a)^4 * (c - b)^1 + (1614 : ℝ) * (b - a)^3 * (c - b)^2 + (1341 : ℝ) * (b - a)^2 * (c - b)^3 + (654 : ℝ) * (b - a)^1 * (c - b)^4 + (120 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (120*a^5 + 426*a^4*b + 54*a^4*c + 315*a^3*b^2 - 120*a^3*b*c - 75*a^3*c^2 - 75*a^2*b^3 - 720*a^2*b^2*c - 720*a^2*b*c^2 + 315*a^2*c^3 + 54*a*b^4 - 120*a*b^3*c - 720*a*b^2*c^2 - 120*a*b*c^3 + 426*a*c^4 + 120*b^5 + 426*b^4*c + 315*b^3*c^2 - 75*b^2*c^3 + 54*b*c^4 + 120*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (3240 : ℝ) * a^3 * (c - a)^2 + (3240 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (3240 : ℝ) * a^3 * (b - c)^2 + (6480 : ℝ) * a^2 * (c - a)^3 + (11421 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (11421 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (3240 : ℝ) * a^2 * (b - c)^3 + (4320 : ℝ) * a^1 * (c - a)^4 + (10908 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (13122 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (6534 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (1080 : ℝ) * a^1 * (b - c)^4 + (960 : ℝ) * (c - a)^5 + (3153 : ℝ) * (c - a)^4 * (b - c)^1 + (4626 : ℝ) * (c - a)^3 * (b - c)^2 + (3219 : ℝ) * (c - a)^2 * (b - c)^3 + (1026 : ℝ) * (c - a)^1 * (b - c)^4 + (120 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (120*a^5 + 426*a^4*b + 54*a^4*c + 315*a^3*b^2 - 120*a^3*b*c - 75*a^3*c^2 - 75*a^2*b^3 - 720*a^2*b^2*c - 720*a^2*b*c^2 + 315*a^2*c^3 + 54*a*b^4 - 120*a*b^3*c - 720*a*b^2*c^2 - 120*a*b*c^3 + 426*a*c^4 + 120*b^5 + 426*b^4*c + 315*b^3*c^2 - 75*b^2*c^3 + 54*b*c^4 + 120*c^5) := by
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
  have hn : 0 ≤ (120*a^5 + 426*a^4*b + 54*a^4*c + 315*a^3*b^2 - 120*a^3*b*c - 75*a^3*c^2 - 75*a^2*b^3 - 720*a^2*b^2*c - 720*a^2*b*c^2 + 315*a^2*c^3 + 54*a*b^4 - 120*a*b^3*c - 720*a*b^2*c^2 - 120*a*b*c^3 + 426*a*c^4 + 120*b^5 + 426*b^4*c + 315*b^3*c^2 - 75*b^2*c^3 + 54*b*c^4 + 120*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a)) ≥ 4 * (1 / (3 * a + 4 * b + 5 * c) + 1 / (3 * b + 4 * c + 5 * a) + 1 / (3 * c + 4 * a + 5 * b))) := @solution
#print axioms solution
