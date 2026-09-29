-- Prove2me | solution 1 for WorkbookSource.plus_37156
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:58:32.942702+00:00
-- url     : https://prove2.me/submissions/2350d4ca-f122-48f0-b433-9cd47ca6e98d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (3 * a + 2 / b) * (3 * b + 2 / c) * (3 * c + 2 / a) ≥ 125   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^6/729 + 52*a^5*b/243 + 52*a^5*c/243 + 184*a^4*b^2/243 - 235*a^4*b*c/243 + 184*a^4*c^2/243 + 808*a^3*b^3/729 - 965*a^3*b^2*c/243 - 965*a^3*b*c^2/243 + 808*a^3*c^3/729 + 184*a^2*b^4/243 - 965*a^2*b^3*c/243 + 1421*a^2*b^2*c^2/81 - 965*a^2*b*c^3/243 + 184*a^2*c^4/243 + 52*a*b^5/243 - 235*a*b^4*c/243 - 965*a*b^3*c^2/243 - 965*a*b^2*c^3/243 - 235*a*b*c^4/243 + 52*a*c^5/243 + 8*b^6/729 + 52*b^5*c/243 + 184*b^4*c^2/243 + 808*b^3*c^3/729 + 184*b^2*c^4/243 + 52*b*c^5/243 + 8*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5/3 : ℝ) * a^4 * (b - a)^2 + (5/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (5/3 : ℝ) * a^4 * (c - b)^2 + (154/27 : ℝ) * a^3 * (b - a)^3 + (77/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (43/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (26/27 : ℝ) * a^3 * (c - b)^3 + (269/27 : ℝ) * a^2 * (b - a)^4 + (538/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (154/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (193/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (77/27 : ℝ) * a^2 * (c - b)^4 + (728/81 : ℝ) * a^1 * (b - a)^5 + (1820/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1958/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1117/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (331/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (40/81 : ℝ) * a^1 * (c - b)^5 + (2240/729 : ℝ) * (b - a)^6 + (2240/243 : ℝ) * (b - a)^5 * (c - b)^1 + (2656/243 : ℝ) * (b - a)^4 * (c - b)^2 + (4736/729 : ℝ) * (b - a)^3 * (c - b)^3 + (484/243 : ℝ) * (b - a)^2 * (c - b)^4 + (68/243 : ℝ) * (b - a)^1 * (c - b)^5 + (8/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^6/729 + 52*a^5*b/243 + 52*a^5*c/243 + 184*a^4*b^2/243 - 235*a^4*b*c/243 + 184*a^4*c^2/243 + 808*a^3*b^3/729 - 965*a^3*b^2*c/243 - 965*a^3*b*c^2/243 + 808*a^3*c^3/729 + 184*a^2*b^4/243 - 965*a^2*b^3*c/243 + 1421*a^2*b^2*c^2/81 - 965*a^2*b*c^3/243 + 184*a^2*c^4/243 + 52*a*b^5/243 - 235*a*b^4*c/243 - 965*a*b^3*c^2/243 - 965*a*b^2*c^3/243 - 235*a*b*c^4/243 + 52*a*c^5/243 + 8*b^6/729 + 52*b^5*c/243 + 184*b^4*c^2/243 + 808*b^3*c^3/729 + 184*b^2*c^4/243 + 52*b*c^5/243 + 8*c^6/729) := by
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
  have he : (27*a^2*b^2*c^2 + 18*a^2*b*c + 18*a*b^2*c + 18*a*b*c^2 - 125*a*b*c + 12*a*b + 12*a*c + 12*b*c + 8) = (8*a^6/729 + 52*a^5*b/243 + 52*a^5*c/243 + 184*a^4*b^2/243 - 235*a^4*b*c/243 + 184*a^4*c^2/243 + 808*a^3*b^3/729 - 965*a^3*b^2*c/243 - 965*a^3*b*c^2/243 + 808*a^3*c^3/729 + 184*a^2*b^4/243 - 965*a^2*b^3*c/243 + 1421*a^2*b^2*c^2/81 - 965*a^2*b*c^3/243 + 184*a^2*c^4/243 + 52*a*b^5/243 - 235*a*b^4*c/243 - 965*a*b^3*c^2/243 - 965*a*b^2*c^3/243 - 235*a*b*c^4/243 + 52*a*c^5/243 + 8*b^6/729 + 52*b^5*c/243 + 184*b^4*c^2/243 + 808*b^3*c^3/729 + 184*b^2*c^4/243 + 52*b*c^5/243 + 8*c^6/729) := by
    linear_combination (-8*a^5/729 - 148*a^4*b/729 - 148*a^4*c/729 - 8*a^4/243 - 404*a^3*b^2/729 + 1001*a^3*b*c/729 - 140*a^3*b/243 - 404*a^3*c^2/729 - 140*a^3*c/243 - 8*a^3/81 - 404*a^2*b^3/729 + 766*a^2*b^2*c/243 - 88*a^2*b^2/81 + 766*a^2*b*c^2/243 + 427*a^2*b*c/81 - 44*a^2*b/27 - 404*a^2*c^3/729 - 88*a^2*c^2/81 - 44*a^2*c/27 - 8*a^2/27 - 148*a*b^4/729 + 1001*a*b^3*c/729 - 140*a*b^3/243 + 766*a*b^2*c^2/243 + 427*a*b^2*c/81 - 44*a*b^2/27 + 1001*a*b*c^3/729 + 427*a*b*c^2/81 + 1001*a*b*c/27 - 124*a*b/27 - 148*a*c^4/729 - 140*a*c^3/243 - 44*a*c^2/27 - 124*a*c/27 - 8*a/9 - 8*b^5/729 - 148*b^4*c/729 - 8*b^4/243 - 404*b^3*c^2/729 - 140*b^3*c/243 - 8*b^3/81 - 404*b^2*c^3/729 - 88*b^2*c^2/81 - 44*b^2*c/27 - 8*b^2/27 - 148*b*c^4/729 - 140*b*c^3/243 - 44*b*c^2/27 - 124*b*c/27 - 8*b/9 - 8*c^5/729 - 8*c^4/243 - 8*c^3/81 - 8*c^2/27 - 8*c/9 - 8/3) * hab
  have hn : 0 ≤ (27*a^2*b^2*c^2 + 18*a^2*b*c + 18*a*b^2*c + 18*a*b*c^2 - 125*a*b*c + 12*a*b + 12*a*c + 12*b*c + 8) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (3 * a + 2 / b) * (3 * b + 2 / c) * (3 * c + 2 / a) ≥ 125) := @solution
#print axioms solution
