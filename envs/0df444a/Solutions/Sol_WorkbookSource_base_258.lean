-- Prove2me | solution 1 for WorkbookSource.base_258
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:24:50.117842+00:00
-- url     : https://prove2.me/submissions/48907032-d38a-492f-8da5-0a095df7fe2e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : a * b + a * c + a * d + b * c + b * d + c * d + (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) / (a + b + c + d) ≥ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 3 * (a + b + c - d) * (a + b + d - c) * (a + c + d - b) * (b + c + d - a) / (a + b + c + d) ^ 2  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (3*a^4 - 6*a^2*b^2 + 3*a^2*b*c + 3*a^2*b*d - 6*a^2*c^2 + 3*a^2*c*d - 6*a^2*d^2 + 3*a*b^2*c + 3*a*b^2*d + 3*a*b*c^2 - 12*a*b*c*d + 3*a*b*d^2 + 3*a*c^2*d + 3*a*c*d^2 + 3*b^4 - 6*b^2*c^2 + 3*b^2*c*d - 6*b^2*d^2 + 3*b*c^2*d + 3*b*c*d^2 + 3*c^4 - 6*c^2*d^2 + 3*d^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^2 * (b - a)^2 + (12 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^2 * (b - a)^1 * (d - c)^1 + (12 : ℝ) * a^2 * (c - b)^2 + (12 : ℝ) * a^2 * (c - b)^1 * (d - c)^1 + (9 : ℝ) * a^2 * (d - c)^2 + (6 : ℝ) * a^1 * (b - a)^3 + (12 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (6 : ℝ) * a^1 * (b - a)^2 * (d - c)^1 + (30 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (30 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 * (d - c)^1 + (24 : ℝ) * a^1 * (b - a)^1 * (d - c)^2 + (12 : ℝ) * a^1 * (c - b)^3 + (18 : ℝ) * a^1 * (c - b)^2 * (d - c)^1 + (30 : ℝ) * a^1 * (c - b)^1 * (d - c)^2 + (12 : ℝ) * a^1 * (d - c)^3 + (9 : ℝ) * (b - a)^2 * (c - b)^2 + (9 : ℝ) * (b - a)^2 * (c - b)^1 * (d - c)^1 + (9 : ℝ) * (b - a)^2 * (d - c)^2 + (6 : ℝ) * (b - a)^1 * (c - b)^3 + (9 : ℝ) * (b - a)^1 * (c - b)^2 * (d - c)^1 + (27 : ℝ) * (b - a)^1 * (c - b)^1 * (d - c)^2 + (12 : ℝ) * (b - a)^1 * (d - c)^3 + (12 : ℝ) * (c - b)^2 * (d - c)^2 + (12 : ℝ) * (c - b)^1 * (d - c)^3 + (3 : ℝ) * (d - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^4 - 6*a^2*b^2 + 3*a^2*b*c + 3*a^2*b*d - 6*a^2*c^2 + 3*a^2*c*d - 6*a^2*d^2 + 3*a*b^2*c + 3*a*b^2*d + 3*a*b*c^2 - 12*a*b*c*d + 3*a*b*d^2 + 3*a*c^2*d + 3*a*c*d^2 + 3*b^4 - 6*b^2*c^2 + 3*b^2*c*d - 6*b^2*d^2 + 3*b*c^2*d + 3*b*c*d^2 + 3*c^4 - 6*c^2*d^2 + 3*d^4) := by
    rcases le_total b a with hcase1 | hcase1
    ·
      rcases le_total c b with hcase2 | hcase2
      ·
        rcases le_total d c with hcase3 | hcase3
        ·
          convert haux0 d c b a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase4 | hcase4
          ·
            convert haux0 c d b a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase5 | hcase5
            ·
              convert haux0 c b d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux0 c b a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c a with hcase6 | hcase6
        ·
          rcases le_total d b with hcase7 | hcase7
          ·
            convert haux0 d b c a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase8 | hcase8
            ·
              convert haux0 b d c a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d a with hcase9 | hcase9
              ·
                convert haux0 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 b c a d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase10 | hcase10
          ·
            convert haux0 d b a c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase11 | hcase11
            ·
              convert haux0 b d a c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase12 | hcase12
              ·
                convert haux0 b a d c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 b a c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    ·
      rcases le_total c a with hcase13 | hcase13
      ·
        rcases le_total d c with hcase14 | hcase14
        ·
          convert haux0 d c a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase15 | hcase15
          ·
            convert haux0 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase16 | hcase16
            ·
              convert haux0 c a d b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux0 c a b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c b with hcase17 | hcase17
        ·
          rcases le_total d a with hcase18 | hcase18
          ·
            convert haux0 d a c b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase19 | hcase19
            ·
              convert haux0 a d c b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d b with hcase20 | hcase20
              ·
                convert haux0 a c d b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 a c b d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase21 | hcase21
          ·
            convert haux0 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase22 | hcase22
            ·
              convert haux0 a d b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase23 | hcase23
              ·
                convert haux0 a b d c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (3*a^4 - 6*a^2*b^2 + 3*a^2*b*c + 3*a^2*b*d - 6*a^2*c^2 + 3*a^2*c*d - 6*a^2*d^2 + 3*a*b^2*c + 3*a*b^2*d + 3*a*b*c^2 - 12*a*b*c*d + 3*a*b*d^2 + 3*a*c^2*d + 3*a*c*d^2 + 3*b^4 - 6*b^2*c^2 + 3*b^2*c*d - 6*b^2*d^2 + 3*b*c^2*d + 3*b*c*d^2 + 3*c^4 - 6*c^2*d^2 + 3*d^4) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + b + c + d)^2) := by positivity
  have heqrat : ( a * b + a * c + a * d + b * c + b * d + c * d + (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) / (a + b + c + d) ) - ( a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 3 * (a + b + c - d) * (a + b + d - c) * (a + c + d - b) * (b + c + d - a) / (a + b + c + d) ^ 2  ) = (3*a^4 - 6*a^2*b^2 + 3*a^2*b*c + 3*a^2*b*d - 6*a^2*c^2 + 3*a^2*c*d - 6*a^2*d^2 + 3*a*b^2*c + 3*a*b^2*d + 3*a*b*c^2 - 12*a*b*c*d + 3*a*b*d^2 + 3*a*c^2*d + 3*a*c*d^2 + 3*b^4 - 6*b^2*c^2 + 3*b^2*c*d - 6*b^2*d^2 + 3*b*c^2*d + 3*b*c*d^2 + 3*c^4 - 6*c^2*d^2 + 3*d^4) / ((a + b + c + d)^2) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), a * b + a * c + a * d + b * c + b * d + c * d + (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) / (a + b + c + d) ≥ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 3 * (a + b + c - d) * (a + b + d - c) * (a + c + d - b) * (b + c + d - a) / (a + b + c + d) ^ 2) := @solution
#print axioms solution
