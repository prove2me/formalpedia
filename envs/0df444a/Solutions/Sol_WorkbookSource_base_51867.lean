-- Prove2me | solution 1 for WorkbookSource.base_51867
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:14.091913+00:00
-- url     : https://prove2.me/submissions/d7b5a71a-3344-4d5a-8b7b-9226f771fcef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * b) / (7 + 2 * c ^ 2) + (b * c) / (7 + 2 * a ^ 2) + (c * a) / (7 + 2 * b ^ 2) ≤ 1 / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (1225*a^6/729 + 287*a^5*b/243 + 287*a^5*c/243 + 497*a^4*b^2/243 - 1547*a^4*b*c/243 + 497*a^4*c^2/243 - 5038*a^3*b^3/729 - 28*a^3*b^2*c/243 - 28*a^3*b*c^2/243 - 5038*a^3*c^3/729 + 497*a^2*b^4/243 - 28*a^2*b^3*c/243 + 1306*a^2*b^2*c^2/81 - 28*a^2*b*c^3/243 + 497*a^2*c^4/243 + 287*a*b^5/243 - 1547*a*b^4*c/243 - 28*a*b^3*c^2/243 - 28*a*b^2*c^3/243 - 1547*a*b*c^4/243 + 287*a*c^5/243 + 1225*b^6/729 + 287*b^5*c/243 + 497*b^4*c^2/243 - 5038*b^3*c^3/729 + 497*b^2*c^4/243 + 287*b*c^5/243 + 1225*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (13 : ℝ) * a^4 * (b - a)^2 + (13 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (13 : ℝ) * a^4 * (c - b)^2 + (484/27 : ℝ) * a^3 * (b - a)^3 + (242/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (694/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (920/27 : ℝ) * a^3 * (c - b)^3 + (284/27 : ℝ) * a^2 * (b - a)^4 + (568/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1180/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (3256/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (938/27 : ℝ) * a^2 * (c - b)^4 + (184/27 : ℝ) * a^1 * (b - a)^5 + (460/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (860/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (3410/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (1778/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (112/9 : ℝ) * a^1 * (c - b)^5 + (2116/729 : ℝ) * (b - a)^6 + (2116/243 : ℝ) * (b - a)^5 * (c - b)^1 + (7436/243 : ℝ) * (b - a)^4 * (c - b)^2 + (34036/729 : ℝ) * (b - a)^3 * (c - b)^3 + (8057/243 : ℝ) * (b - a)^2 * (c - b)^4 + (2737/243 : ℝ) * (b - a)^1 * (c - b)^5 + (1225/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (1225*a^6/729 + 287*a^5*b/243 + 287*a^5*c/243 + 497*a^4*b^2/243 - 1547*a^4*b*c/243 + 497*a^4*c^2/243 - 5038*a^3*b^3/729 - 28*a^3*b^2*c/243 - 28*a^3*b*c^2/243 - 5038*a^3*c^3/729 + 497*a^2*b^4/243 - 28*a^2*b^3*c/243 + 1306*a^2*b^2*c^2/81 - 28*a^2*b*c^3/243 + 497*a^2*c^4/243 + 287*a*b^5/243 - 1547*a*b^4*c/243 - 28*a*b^3*c^2/243 - 28*a*b^2*c^3/243 - 1547*a*b*c^4/243 + 287*a*c^5/243 + 1225*b^6/729 + 287*b^5*c/243 + 497*b^4*c^2/243 - 5038*b^3*c^3/729 + 497*b^2*c^4/243 + 287*b*c^5/243 + 1225*c^6/729) := by
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
  have he : (-12*a^3*b^3 - 42*a^3*b - 12*a^3*c^3 - 42*a^3*c + 8*a^2*b^2*c^2 + 28*a^2*b^2 + 28*a^2*c^2 + 98*a^2 - 42*a*b^3 - 147*a*b - 42*a*c^3 - 147*a*c - 12*b^3*c^3 - 42*b^3*c + 28*b^2*c^2 + 98*b^2 - 42*b*c^3 - 147*b*c + 98*c^2 + 343) = (1225*a^6/729 + 287*a^5*b/243 + 287*a^5*c/243 + 497*a^4*b^2/243 - 1547*a^4*b*c/243 + 497*a^4*c^2/243 - 5038*a^3*b^3/729 - 28*a^3*b^2*c/243 - 28*a^3*b*c^2/243 - 5038*a^3*c^3/729 + 497*a^2*b^4/243 - 28*a^2*b^3*c/243 + 1306*a^2*b^2*c^2/81 - 28*a^2*b*c^3/243 + 497*a^2*c^4/243 + 287*a*b^5/243 - 1547*a*b^4*c/243 - 28*a*b^3*c^2/243 - 28*a*b^2*c^3/243 - 1547*a*b*c^4/243 + 287*a*c^5/243 + 1225*b^6/729 + 287*b^5*c/243 + 497*b^4*c^2/243 - 5038*b^3*c^3/729 + 497*b^2*c^4/243 + 287*b*c^5/243 + 1225*c^6/729) := by
    linear_combination (-1225*a^5/729 + 364*a^4*b/729 + 364*a^4*c/729 - 1225*a^4/243 - 1855*a^3*b^2/729 + 3913*a^3*b*c/729 + 1589*a^3*b/243 - 1855*a^3*c^2/729 + 1589*a^3*c/243 - 1225*a^3/81 - 1855*a^2*b^3/729 - 658*a^2*b^2*c/243 - 1148*a^2*b^2/81 - 658*a^2*b*c^2/243 + 245*a^2*b*c/81 - 196*a^2*b/27 - 1855*a^2*c^3/729 - 1148*a^2*c^2/81 - 196*a^2*c/27 - 1225*a^2/27 + 364*a*b^4/729 + 3913*a*b^3*c/729 + 1589*a*b^3/243 - 658*a*b^2*c^2/243 + 245*a*b^2*c/81 - 196*a*b^2/27 + 3913*a*b*c^3/729 + 245*a*b*c^2/81 + 637*a*b*c/27 + 637*a*b/27 + 364*a*c^4/729 + 1589*a*c^3/243 - 196*a*c^2/27 + 637*a*c/27 - 343*a/9 - 1225*b^5/729 + 364*b^4*c/729 - 1225*b^4/243 - 1855*b^3*c^2/729 + 1589*b^3*c/243 - 1225*b^3/81 - 1855*b^2*c^3/729 - 1148*b^2*c^2/81 - 196*b^2*c/27 - 1225*b^2/27 + 364*b*c^4/729 + 1589*b*c^3/243 - 196*b*c^2/27 + 637*b*c/27 - 343*b/9 - 1225*c^5/729 - 1225*c^4/243 - 1225*c^3/81 - 1225*c^2/27 - 343*c/9 - 343/3) * hab
  have hn : 0 ≤ (-12*a^3*b^3 - 42*a^3*b - 12*a^3*c^3 - 42*a^3*c + 8*a^2*b^2*c^2 + 28*a^2*b^2 + 28*a^2*c^2 + 98*a^2 - 42*a*b^3 - 147*a*b - 42*a*c^3 - 147*a*c - 12*b^3*c^3 - 42*b^3*c + 28*b^2*c^2 + 98*b^2 - 42*b*c^3 - 147*b*c + 98*c^2 + 343) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a * b) / (7 + 2 * c ^ 2) + (b * c) / (7 + 2 * a ^ 2) + (c * a) / (7 + 2 * b ^ 2) ≤ 1 / 3) := @solution
#print axioms solution
