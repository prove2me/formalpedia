-- Prove2me | solution 1 for WorkbookSource.base_10295
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:34:33.703211+00:00
-- url     : https://prove2.me/submissions/78c82f38-e86d-45c2-866e-8433b4b85e98

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (11 + a^2) + 1 / (11 + b^2) + 1 / (11 + c^2) ≤ 1 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (176*a^6/729 + 154*a^5*b/243 + 154*a^5*c/243 + 277*a^4*b^2/243 - 22*a^4*b*c/243 + 277*a^4*c^2/243 + 1090*a^3*b^3/729 - 458*a^3*b^2*c/243 - 458*a^3*b*c^2/243 + 1090*a^3*c^3/729 + 277*a^2*b^4/243 - 458*a^2*b^3*c/243 - 346*a^2*b^2*c^2/81 - 458*a^2*b*c^3/243 + 277*a^2*c^4/243 + 154*a*b^5/243 - 22*a*b^4*c/243 - 458*a*b^3*c^2/243 - 458*a*b^2*c^3/243 - 22*a*b*c^4/243 + 154*a*c^5/243 + 176*b^6/729 + 154*b^5*c/243 + 277*b^4*c^2/243 + 1090*b^3*c^3/729 + 277*b^2*c^4/243 + 154*b*c^5/243 + 176*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (64/3 : ℝ) * a^4 * (b - a)^2 + (64/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (64/3 : ℝ) * a^4 * (c - b)^2 + (1616/27 : ℝ) * a^3 * (b - a)^3 + (808/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (728/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (688/27 : ℝ) * a^3 * (c - b)^3 + (1720/27 : ℝ) * a^2 * (b - a)^4 + (3440/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1136/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1688/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (328/27 : ℝ) * a^2 * (c - b)^4 + (2468/81 : ℝ) * a^1 * (b - a)^5 + (6170/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (7124/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (4516/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (1534/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (220/81 : ℝ) * a^1 * (c - b)^5 + (4028/729 : ℝ) * (b - a)^6 + (4028/243 : ℝ) * (b - a)^5 * (c - b)^1 + (5449/243 : ℝ) * (b - a)^4 * (c - b)^2 + (12554/729 : ℝ) * (b - a)^3 * (c - b)^3 + (1927/243 : ℝ) * (b - a)^2 * (c - b)^4 + (506/243 : ℝ) * (b - a)^1 * (c - b)^5 + (176/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (176*a^6/729 + 154*a^5*b/243 + 154*a^5*c/243 + 277*a^4*b^2/243 - 22*a^4*b*c/243 + 277*a^4*c^2/243 + 1090*a^3*b^3/729 - 458*a^3*b^2*c/243 - 458*a^3*b*c^2/243 + 1090*a^3*c^3/729 + 277*a^2*b^4/243 - 458*a^2*b^3*c/243 - 346*a^2*b^2*c^2/81 - 458*a^2*b*c^3/243 + 277*a^2*c^4/243 + 154*a*b^5/243 - 22*a*b^4*c/243 - 458*a*b^3*c^2/243 - 458*a*b^2*c^3/243 - 22*a*b*c^4/243 + 154*a*c^5/243 + 176*b^6/729 + 154*b^5*c/243 + 277*b^4*c^2/243 + 1090*b^3*c^3/729 + 277*b^2*c^4/243 + 154*b*c^5/243 + 176*c^6/729) := by
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
  have he : (a^2*b^2*c^2 + 7*a^2*b^2 + 7*a^2*c^2 + 33*a^2 + 7*b^2*c^2 + 33*b^2 + 33*c^2 - 121) = (176*a^6/729 + 154*a^5*b/243 + 154*a^5*c/243 + 277*a^4*b^2/243 - 22*a^4*b*c/243 + 277*a^4*c^2/243 + 1090*a^3*b^3/729 - 458*a^3*b^2*c/243 - 458*a^3*b*c^2/243 + 1090*a^3*c^3/729 + 277*a^2*b^4/243 - 458*a^2*b^3*c/243 - 346*a^2*b^2*c^2/81 - 458*a^2*b*c^3/243 + 277*a^2*c^4/243 + 154*a*b^5/243 - 22*a*b^4*c/243 - 458*a*b^3*c^2/243 - 458*a*b^2*c^3/243 - 22*a*b*c^4/243 + 154*a*c^5/243 + 176*b^6/729 + 154*b^5*c/243 + 277*b^4*c^2/243 + 1090*b^3*c^3/729 + 277*b^2*c^4/243 + 154*b*c^5/243 + 176*c^6/729) := by
    linear_combination (-176*a^5/729 - 286*a^4*b/729 - 286*a^4*c/729 - 176*a^4/243 - 545*a^3*b^2/729 + 638*a^3*b*c/729 - 110*a^3*b/243 - 545*a^3*c^2/729 - 110*a^3*c/243 - 176*a^3/81 - 545*a^2*b^3/729 + 427*a^2*b^2*c/243 - 145*a^2*b^2/81 + 427*a^2*b*c^2/243 + 286*a^2*b*c/81 + 22*a^2*b/27 - 545*a^2*c^3/729 - 145*a^2*c^2/81 + 22*a^2*c/27 - 176*a^2/27 - 286*a*b^4/729 + 638*a*b^3*c/729 - 110*a*b^3/243 + 427*a*b^2*c^2/243 + 286*a*b^2*c/81 + 22*a*b^2/27 + 638*a*b*c^3/729 + 286*a*b*c^2/81 + 242*a*b*c/27 + 242*a*b/27 - 286*a*c^4/729 - 110*a*c^3/243 + 22*a*c^2/27 + 242*a*c/27 + 121*a/9 - 176*b^5/729 - 286*b^4*c/729 - 176*b^4/243 - 545*b^3*c^2/729 - 110*b^3*c/243 - 176*b^3/81 - 545*b^2*c^3/729 - 145*b^2*c^2/81 + 22*b^2*c/27 - 176*b^2/27 - 286*b*c^4/729 - 110*b*c^3/243 + 22*b*c^2/27 + 242*b*c/27 + 121*b/9 - 176*c^5/729 - 176*c^4/243 - 176*c^3/81 - 176*c^2/27 + 121*c/9 + 121/3) * habc
  have hn : 0 ≤ (a^2*b^2*c^2 + 7*a^2*b^2 + 7*a^2*c^2 + 33*a^2 + 7*b^2*c^2 + 33*b^2 + 33*c^2 - 121) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 1 / (11 + a^2) + 1 / (11 + b^2) + 1 / (11 + c^2) ≤ 1 / 4) := @solution
#print axioms solution
