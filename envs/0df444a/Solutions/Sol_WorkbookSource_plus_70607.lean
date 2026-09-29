-- Prove2me | solution 1 for WorkbookSource.plus_70607
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:51:26.330034+00:00
-- url     : https://prove2.me/submissions/60137686-6ba3-46d1-b9a0-cc53c382f417

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 + b^2 + c^2 ≥ (2 + a) / (2 + b) + (2 + b) / (2 + c) + (2 + c) / (2 + a)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (34*a^5/81 + 104*a^4*b/81 + 95*a^4*c/81 + 25*a^3*b^2/81 + 65*a^3*b*c/81 + 16*a^3*c^2/81 + 16*a^2*b^3/81 - 113*a^2*b^2*c/27 - 113*a^2*b*c^2/27 + 25*a^2*c^3/81 + 95*a*b^4/81 + 65*a*b^3*c/81 - 113*a*b^2*c^2/27 + 65*a*b*c^3/81 + 104*a*c^4/81 + 34*b^5/81 + 104*b^4*c/81 + 25*b^3*c^2/81 + 16*b^2*c^3/81 + 95*b*c^4/81 + 34*c^5/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (15 : ℝ) * a^3 * (b - a)^2 + (15 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (15 : ℝ) * a^3 * (c - b)^2 + (89/3 : ℝ) * a^2 * (b - a)^3 + (44 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (45 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (46/3 : ℝ) * a^2 * (c - b)^3 + (170/9 : ℝ) * a^1 * (b - a)^4 + (334/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (127/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (217/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (41/9 : ℝ) * a^1 * (c - b)^4 + (308/81 : ℝ) * (b - a)^5 + (752/81 : ℝ) * (b - a)^4 * (c - b)^1 + (983/81 : ℝ) * (b - a)^3 * (c - b)^2 + (736/81 : ℝ) * (b - a)^2 * (c - b)^3 + (265/81 : ℝ) * (b - a)^1 * (c - b)^4 + (34/81 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (34*a^5/81 + 104*a^4*b/81 + 95*a^4*c/81 + 25*a^3*b^2/81 + 65*a^3*b*c/81 + 16*a^3*c^2/81 + 16*a^2*b^3/81 - 113*a^2*b^2*c/27 - 113*a^2*b*c^2/27 + 25*a^2*c^3/81 + 95*a*b^4/81 + 65*a*b^3*c/81 - 113*a*b^2*c^2/27 + 65*a*b*c^3/81 + 104*a*c^4/81 + 34*b^5/81 + 104*b^4*c/81 + 25*b^3*c^2/81 + 16*b^2*c^3/81 + 95*b*c^4/81 + 34*c^5/81) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (15 : ℝ) * a^3 * (c - a)^2 + (15 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (15 : ℝ) * a^3 * (b - c)^2 + (89/3 : ℝ) * a^2 * (c - a)^3 + (45 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (46 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (46/3 : ℝ) * a^2 * (b - c)^3 + (170/9 : ℝ) * a^1 * (c - a)^4 + (346/9 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (133/3 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (223/9 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (41/9 : ℝ) * a^1 * (b - c)^4 + (308/81 : ℝ) * (c - a)^5 + (788/81 : ℝ) * (c - a)^4 * (b - c)^1 + (1055/81 : ℝ) * (c - a)^3 * (b - c)^2 + (781/81 : ℝ) * (c - a)^2 * (b - c)^3 + (274/81 : ℝ) * (c - a)^1 * (b - c)^4 + (34/81 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (34*a^5/81 + 104*a^4*b/81 + 95*a^4*c/81 + 25*a^3*b^2/81 + 65*a^3*b*c/81 + 16*a^3*c^2/81 + 16*a^2*b^3/81 - 113*a^2*b^2*c/27 - 113*a^2*b*c^2/27 + 25*a^2*c^3/81 + 95*a*b^4/81 + 65*a*b^3*c/81 - 113*a*b^2*c^2/27 + 65*a*b*c^3/81 + 104*a*c^4/81 + 34*b^5/81 + 104*b^4*c/81 + 25*b^3*c^2/81 + 16*b^2*c^3/81 + 95*b*c^4/81 + 34*c^5/81) := by
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
  have he : (a^3*b*c + 2*a^3*b + 2*a^3*c + 4*a^3 + 2*a^2*b*c + 4*a^2*b + 3*a^2*c + 6*a^2 + a*b^3*c + 2*a*b^3 + 2*a*b^2*c + 3*a*b^2 + a*b*c^3 + 2*a*b*c^2 - 4*a*b + 2*a*c^3 + 4*a*c^2 - 4*a*c - 12*a + 2*b^3*c + 4*b^3 + 4*b^2*c + 6*b^2 + 2*b*c^3 + 3*b*c^2 - 4*b*c - 12*b + 4*c^3 + 6*c^2 - 12*c - 24) = (34*a^5/81 + 104*a^4*b/81 + 95*a^4*c/81 + 25*a^3*b^2/81 + 65*a^3*b*c/81 + 16*a^3*c^2/81 + 16*a^2*b^3/81 - 113*a^2*b^2*c/27 - 113*a^2*b*c^2/27 + 25*a^2*c^3/81 + 95*a*b^4/81 + 65*a*b^3*c/81 - 113*a*b^2*c^2/27 + 65*a*b*c^3/81 + 104*a*c^4/81 + 34*b^5/81 + 104*b^4*c/81 + 25*b^3*c^2/81 + 16*b^2*c^3/81 + 95*b*c^4/81 + 34*c^5/81) := by
    linear_combination (-34*a^4/81 - 70*a^3*b/81 - 61*a^3*c/81 - 34*a^3/27 + 5*a^2*b^2/9 + 49*a^2*b*c/27 + 2*a^2*b/3 + 5*a^2*c^2/9 + a^2*c + 2*a^2/9 - 61*a*b^3/81 + 49*a*b^2*c/27 + a*b^2 + 49*a*b*c^2/27 + 52*a*b*c/9 + 52*a*b/9 - 70*a*c^3/81 + 2*a*c^2/3 + 52*a*c/9 + 20*a/3 - 34*b^4/81 - 70*b^3*c/81 - 34*b^3/27 + 5*b^2*c^2/9 + 2*b^2*c/3 + 2*b^2/9 - 61*b*c^3/81 + b*c^2 + 52*b*c/9 + 20*b/3 - 34*c^4/81 - 34*c^3/27 + 2*c^2/9 + 20*c/3 + 8) * habc
  have hn : 0 ≤ (a^3*b*c + 2*a^3*b + 2*a^3*c + 4*a^3 + 2*a^2*b*c + 4*a^2*b + 3*a^2*c + 6*a^2 + a*b^3*c + 2*a*b^3 + 2*a*b^2*c + 3*a*b^2 + a*b*c^3 + 2*a*b*c^2 - 4*a*b + 2*a*c^3 + 4*a*c^2 - 4*a*c - 12*a + 2*b^3*c + 4*b^3 + 4*b^2*c + 6*b^2 + 2*b*c^3 + 3*b*c^2 - 4*b*c - 12*b + 4*c^3 + 6*c^2 - 12*c - 24) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a^2 + b^2 + c^2 ≥ (2 + a) / (2 + b) + (2 + b) / (2 + c) + (2 + c) / (2 + a)) := @solution
#print axioms solution
