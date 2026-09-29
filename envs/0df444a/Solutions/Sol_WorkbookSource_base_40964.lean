-- Prove2me | solution 1 for WorkbookSource.base_40964
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:19.678463+00:00
-- url     : https://prove2.me/submissions/28dc4459-ccc7-4509-8bde-2d2d6c9481cf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab: a + b + c = 3) : (2 * a ^ 2 + 3) * (2 * b ^ 2 + 3) * (2 * c ^ 2 + 3) ≥ 125  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (64*a^6/729 + 20*a^5*b/243 + 20*a^5*c/243 + 212*a^4*b^2/243 - 332*a^4*b*c/243 + 212*a^4*c^2/243 + 1280*a^3*b^3/729 - 448*a^3*b^2*c/243 - 448*a^3*b*c^2/243 + 1280*a^3*c^3/729 + 212*a^2*b^4/243 - 448*a^2*b^3*c/243 + 316*a^2*b^2*c^2/81 - 448*a^2*b*c^3/243 + 212*a^2*c^4/243 + 20*a*b^5/243 - 332*a*b^4*c/243 - 448*a*b^3*c^2/243 - 448*a*b^2*c^3/243 - 332*a*b*c^4/243 + 20*a*c^5/243 + 64*b^6/729 + 20*b^5*c/243 + 212*b^4*c^2/243 + 1280*b^3*c^3/729 + 212*b^2*c^4/243 + 20*b*c^5/243 + 64*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20/3 : ℝ) * a^4 * (b - a)^2 + (20/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (20/3 : ℝ) * a^4 * (c - b)^2 + (592/27 : ℝ) * a^3 * (b - a)^3 + (296/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (184/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (128/27 : ℝ) * a^3 * (c - b)^3 + (764/27 : ℝ) * a^2 * (b - a)^4 + (1528/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (364/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (328/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (68/27 : ℝ) * a^2 * (c - b)^4 + (1360/81 : ℝ) * a^1 * (b - a)^5 + (3400/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (3184/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1376/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (344/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (56/81 : ℝ) * a^1 * (c - b)^5 + (2800/729 : ℝ) * (b - a)^6 + (2800/243 : ℝ) * (b - a)^5 * (c - b)^1 + (3284/243 : ℝ) * (b - a)^4 * (c - b)^2 + (5704/729 : ℝ) * (b - a)^3 * (c - b)^3 + (632/243 : ℝ) * (b - a)^2 * (c - b)^4 + (148/243 : ℝ) * (b - a)^1 * (c - b)^5 + (64/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (64*a^6/729 + 20*a^5*b/243 + 20*a^5*c/243 + 212*a^4*b^2/243 - 332*a^4*b*c/243 + 212*a^4*c^2/243 + 1280*a^3*b^3/729 - 448*a^3*b^2*c/243 - 448*a^3*b*c^2/243 + 1280*a^3*c^3/729 + 212*a^2*b^4/243 - 448*a^2*b^3*c/243 + 316*a^2*b^2*c^2/81 - 448*a^2*b*c^3/243 + 212*a^2*c^4/243 + 20*a*b^5/243 - 332*a*b^4*c/243 - 448*a*b^3*c^2/243 - 448*a*b^2*c^3/243 - 332*a*b*c^4/243 + 20*a*c^5/243 + 64*b^6/729 + 20*b^5*c/243 + 212*b^4*c^2/243 + 1280*b^3*c^3/729 + 212*b^2*c^4/243 + 20*b*c^5/243 + 64*c^6/729) := by
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
  have he : (8*a^2*b^2*c^2 + 12*a^2*b^2 + 12*a^2*c^2 + 18*a^2 + 12*b^2*c^2 + 18*b^2 + 18*c^2 - 98) = (64*a^6/729 + 20*a^5*b/243 + 20*a^5*c/243 + 212*a^4*b^2/243 - 332*a^4*b*c/243 + 212*a^4*c^2/243 + 1280*a^3*b^3/729 - 448*a^3*b^2*c/243 - 448*a^3*b*c^2/243 + 1280*a^3*c^3/729 + 212*a^2*b^4/243 - 448*a^2*b^3*c/243 + 316*a^2*b^2*c^2/81 - 448*a^2*b*c^3/243 + 212*a^2*c^4/243 + 20*a*b^5/243 - 332*a*b^4*c/243 - 448*a*b^3*c^2/243 - 448*a*b^2*c^3/243 - 332*a*b*c^4/243 + 20*a*c^5/243 + 64*b^6/729 + 20*b^5*c/243 + 212*b^4*c^2/243 + 1280*b^3*c^3/729 + 212*b^2*c^4/243 + 20*b*c^5/243 + 64*c^6/729) := by
    linear_combination (-64*a^5/729 + 4*a^4*b/729 + 4*a^4*c/729 - 64*a^4/243 - 640*a^3*b^2/729 + 988*a^3*b*c/729 + 68*a^3*b/243 - 640*a^3*c^2/729 + 68*a^3*c/243 - 64*a^3/81 - 640*a^2*b^3/729 + 332*a^2*b^2*c/243 - 236*a^2*b^2/81 + 332*a^2*b*c^2/243 + 284*a^2*b*c/81 + 44*a^2*b/27 - 640*a^2*c^3/729 - 236*a^2*c^2/81 + 44*a^2*c/27 - 64*a^2/27 + 4*a*b^4/729 + 988*a*b^3*c/729 + 68*a*b^3/243 + 332*a*b^2*c^2/243 + 284*a*b^2*c/81 + 44*a*b^2/27 + 988*a*b*c^3/729 + 284*a*b*c^2/81 + 196*a*b*c/27 + 196*a*b/27 + 4*a*c^4/729 + 68*a*c^3/243 + 44*a*c^2/27 + 196*a*c/27 + 98*a/9 - 64*b^5/729 + 4*b^4*c/729 - 64*b^4/243 - 640*b^3*c^2/729 + 68*b^3*c/243 - 64*b^3/81 - 640*b^2*c^3/729 - 236*b^2*c^2/81 + 44*b^2*c/27 - 64*b^2/27 + 4*b*c^4/729 + 68*b*c^3/243 + 44*b*c^2/27 + 196*b*c/27 + 98*b/9 - 64*c^5/729 - 64*c^4/243 - 64*c^3/81 - 64*c^2/27 + 98*c/9 + 98/3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab: a + b + c = 3), (2 * a ^ 2 + 3) * (2 * b ^ 2 + 3) * (2 * c ^ 2 + 3) ≥ 125) := @solution
#print axioms solution
