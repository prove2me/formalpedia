-- Prove2me | solution 1 for WorkbookSource.base_36191
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T08:51:55.42219+00:00
-- url     : https://prove2.me/submissions/1fe7fcbd-e97a-4fba-9eb2-34cf26bd012e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a - b) / (a + 2 * b + c) + (b - c) / (b + 2 * c + d) + (c - d) / (c + 2 * d + a) + (d - a) / (d + 2 * a + b) ≥ 0  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (3*a^3*b + a^3*d + 2*a^2*b^2 - 5*a^2*b*c + 4*a^2*b*d + a^2*c*d + 2*a^2*d^2 + a*b^3 + 4*a*b^2*c + a*b^2*d + a*b*c^2 - 24*a*b*c*d - 5*a*b*d^2 - 5*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 2*b^2*c^2 - 5*b^2*c*d + b*c^3 + 4*b*c^2*d + b*c*d^2 + 3*c^3*d + 2*c^2*d^2 + c*d^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((b - a))*(16*((b - a)) + 32*((c - b))) + ((c - b))*(32*((c - b)) + 32*((d - c))) + 16*((d - c))^2) + ((b - a))*(((b - a))*(28*((b - a)) + 72*((c - b)) + 12*((d - c))) + ((c - b))*(80*((c - b)) + 64*((d - c))) + 20*((d - c))^2) + ((c - b))*(((c - b))*(32*((c - b)) + 48*((d - c))) + 24*((d - c))^2) + 4*((d - c))^3) + ((b - a))*(((b - a))*(((b - a))*(12*((b - a)) + 39*((c - b)) + 11*((d - c))) + ((c - b))*(51*((c - b)) + 37*((d - c))) + 6*((d - c))^2) + ((c - b))*(((c - b))*(30*((c - b)) + 36*((d - c))) + 11*((d - c))^2) + ((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(6*((c - b)) + 10*((d - c))) + 5*((d - c))^2) + ((d - c))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ d) (hord3 : d ≤ c) : 0 ≤ (3*a^3*b + a^3*d + 2*a^2*b^2 - 5*a^2*b*c + 4*a^2*b*d + a^2*c*d + 2*a^2*d^2 + a*b^3 + 4*a*b^2*c + a*b^2*d + a*b*c^2 - 24*a*b*c*d - 5*a*b*d^2 - 5*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 2*b^2*c^2 - 5*b^2*c*d + b*c^3 + 4*b*c^2*d + b*c*d^2 + 3*c^3*d + 2*c^2*d^2 + c*d^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (d - b) := by linarith
    have hdiff3 : 0 ≤ (c - d) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((b - a))*(16*((b - a)) + 32*((d - b)) + 32*((c - d))) + ((d - b))*(32*((d - b)) + 32*((c - d))) + 16*((c - d))^2) + ((b - a))*(((b - a))*(28*((b - a)) + 72*((d - b)) + 60*((c - d))) + ((d - b))*(80*((d - b)) + 96*((c - d))) + 36*((c - d))^2) + ((d - b))*(((d - b))*(32*((d - b)) + 48*((c - d))) + 24*((c - d))^2) + 4*((c - d))^3) + ((b - a))*(((b - a))*(((b - a))*(12*((b - a)) + 39*((d - b)) + 28*((c - d))) + ((d - b))*(51*((d - b)) + 65*((c - d))) + 20*((c - d))^2) + ((d - b))*(((d - b))*(30*((d - b)) + 54*((c - d))) + 29*((c - d))^2) + 4*((c - d))^3) + ((d - b))*(((d - b))*(((d - b))*(6*((d - b)) + 14*((c - d))) + 11*((c - d))^2) + 3*((c - d))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) (hord3 : b ≤ d) : 0 ≤ (3*a^3*b + a^3*d + 2*a^2*b^2 - 5*a^2*b*c + 4*a^2*b*d + a^2*c*d + 2*a^2*d^2 + a*b^3 + 4*a*b^2*c + a*b^2*d + a*b*c^2 - 24*a*b*c*d - 5*a*b*d^2 - 5*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 2*b^2*c^2 - 5*b^2*c*d + b*c^3 + 4*b*c^2*d + b*c*d^2 + 3*c^3*d + 2*c^2*d^2 + c*d^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hdiff3 : 0 ≤ (d - b) := by linarith
    have hpos : 0 ≤ (a)*((a)*(16*((c - a))^2 + 16*((d - b))^2) + ((c - a))*(((c - a))*(28*((c - a)) + 24*((b - c)) + 12*((d - b))) + 20*((d - b))^2) + 8*((b - c))*((d - b))^2 + 4*((d - b))^3) + ((c - a))*(((c - a))*(((c - a))*(12*((c - a)) + 20*((b - c)) + 11*((d - b))) + ((b - c))*(8*((b - c)) + 8*((d - b))) + 6*((d - b))^2) + 4*((b - c))*((d - b))^2 + ((d - b))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux3 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ d) (hord3 : d ≤ b) : 0 ≤ (3*a^3*b + a^3*d + 2*a^2*b^2 - 5*a^2*b*c + 4*a^2*b*d + a^2*c*d + 2*a^2*d^2 + a*b^3 + 4*a*b^2*c + a*b^2*d + a*b*c^2 - 24*a*b*c*d - 5*a*b*d^2 - 5*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 2*b^2*c^2 - 5*b^2*c*d + b*c^3 + 4*b*c^2*d + b*c*d^2 + 3*c^3*d + 2*c^2*d^2 + c*d^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (d - c) := by linarith
    have hdiff3 : 0 ≤ (b - d) := by linarith
    have hpos : 0 ≤ (a)*((a)*(16*((c - a))^2 + 16*((b - d))^2) + ((c - a))*(((c - a))*(28*((c - a)) + 24*((d - c)) + 12*((b - d))) + 20*((b - d))^2) + 8*((d - c))*((b - d))^2 + 4*((b - d))^3) + ((c - a))*(((c - a))*(((c - a))*(12*((c - a)) + 20*((d - c)) + 9*((b - d))) + ((d - c))*(8*((d - c)) + 8*((b - d))) + 6*((b - d))^2) + 4*((d - c))*((b - d))^2 + 3*((b - d))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux4 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ d) (hord2 : d ≤ b) (hord3 : b ≤ c) : 0 ≤ (3*a^3*b + a^3*d + 2*a^2*b^2 - 5*a^2*b*c + 4*a^2*b*d + a^2*c*d + 2*a^2*d^2 + a*b^3 + 4*a*b^2*c + a*b^2*d + a*b*c^2 - 24*a*b*c*d - 5*a*b*d^2 - 5*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 2*b^2*c^2 - 5*b^2*c*d + b*c^3 + 4*b*c^2*d + b*c*d^2 + 3*c^3*d + 2*c^2*d^2 + c*d^3) := by
    have hdiff1 : 0 ≤ (d - a) := by linarith
    have hdiff2 : 0 ≤ (b - d) := by linarith
    have hdiff3 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((d - a))*(16*((d - a)) + 32*((b - d)) + 32*((c - b))) + ((b - d))*(32*((b - d)) + 32*((c - b))) + 16*((c - b))^2) + ((d - a))*(((d - a))*(28*((d - a)) + 72*((b - d)) + 60*((c - b))) + ((b - d))*(80*((b - d)) + 96*((c - b))) + 36*((c - b))^2) + ((b - d))*(((b - d))*(32*((b - d)) + 48*((c - b))) + 24*((c - b))^2) + 4*((c - b))^3) + ((d - a))*(((d - a))*(((d - a))*(12*((d - a)) + 37*((b - d)) + 28*((c - b))) + ((b - d))*(45*((b - d)) + 59*((c - b))) + 20*((c - b))^2) + ((b - d))*(((b - d))*(26*((b - d)) + 42*((c - b))) + 23*((c - b))^2) + 4*((c - b))^3) + ((b - d))*(((b - d))*(((b - d))*(6*((b - d)) + 10*((c - b))) + 5*((c - b))^2) + ((c - b))^3) := by positivity
    convert hpos using 1 <;> ring
  have haux5 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ d) (hord2 : d ≤ c) (hord3 : c ≤ b) : 0 ≤ (3*a^3*b + a^3*d + 2*a^2*b^2 - 5*a^2*b*c + 4*a^2*b*d + a^2*c*d + 2*a^2*d^2 + a*b^3 + 4*a*b^2*c + a*b^2*d + a*b*c^2 - 24*a*b*c*d - 5*a*b*d^2 - 5*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 2*b^2*c^2 - 5*b^2*c*d + b*c^3 + 4*b*c^2*d + b*c*d^2 + 3*c^3*d + 2*c^2*d^2 + c*d^3) := by
    have hdiff1 : 0 ≤ (d - a) := by linarith
    have hdiff2 : 0 ≤ (c - d) := by linarith
    have hdiff3 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((d - a))*(16*((d - a)) + 32*((c - d))) + ((c - d))*(32*((c - d)) + 32*((b - c))) + 16*((b - c))^2) + ((d - a))*(((d - a))*(28*((d - a)) + 72*((c - d)) + 12*((b - c))) + ((c - d))*(80*((c - d)) + 64*((b - c))) + 20*((b - c))^2) + ((c - d))*(((c - d))*(32*((c - d)) + 48*((b - c))) + 24*((b - c))^2) + 4*((b - c))^3) + ((d - a))*(((d - a))*(((d - a))*(12*((d - a)) + 37*((c - d)) + 9*((b - c))) + ((c - d))*(45*((c - d)) + 31*((b - c))) + 6*((b - c))^2) + ((c - d))*(((c - d))*(26*((c - d)) + 36*((b - c))) + 17*((b - c))^2) + 3*((b - c))^3) + ((c - d))*(((c - d))*(((c - d))*(6*((c - d)) + 14*((b - c))) + 11*((b - c))^2) + 3*((b - c))^3) := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^3*b + a^3*d + 2*a^2*b^2 - 5*a^2*b*c + 4*a^2*b*d + a^2*c*d + 2*a^2*d^2 + a*b^3 + 4*a*b^2*c + a*b^2*d + a*b*c^2 - 24*a*b*c*d - 5*a*b*d^2 - 5*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 2*b^2*c^2 - 5*b^2*c*d + b*c^3 + 4*b*c^2*d + b*c*d^2 + 3*c^3*d + 2*c^2*d^2 + c*d^3) := by
    rcases le_total b a with hcase1 | hcase1
    ·
      rcases le_total c b with hcase2 | hcase2
      ·
        rcases le_total d c with hcase3 | hcase3
        ·
          convert haux5 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase4 | hcase4
          ·
            convert haux1 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase5 | hcase5
            ·
              convert haux4 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux5 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c a with hcase6 | hcase6
        ·
          rcases le_total d b with hcase7 | hcase7
          ·
            convert haux3 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase8 | hcase8
            ·
              convert haux2 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d a with hcase9 | hcase9
              ·
                convert haux0 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux1 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d b with hcase10 | hcase10
          ·
            convert haux2 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d a with hcase11 | hcase11
            ·
              convert haux3 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase12 | hcase12
              ·
                convert haux5 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux4 b c d a (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
    ·
      rcases le_total c a with hcase13 | hcase13
      ·
        rcases le_total d c with hcase14 | hcase14
        ·
          convert haux4 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase15 | hcase15
          ·
            convert haux0 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase16 | hcase16
            ·
              convert haux2 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              convert haux3 c d a b (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
      ·
        rcases le_total c b with hcase17 | hcase17
        ·
          rcases le_total d a with hcase18 | hcase18
          ·
            convert haux1 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d c with hcase19 | hcase19
            ·
              convert haux5 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d b with hcase20 | hcase20
              ·
                convert haux3 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux2 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
        ·
          rcases le_total d a with hcase21 | hcase21
          ·
            convert haux0 d a b c (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
          ·
            rcases le_total d b with hcase22 | hcase22
            ·
              convert haux4 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
            ·
              rcases le_total d c with hcase23 | hcase23
              ·
                convert haux1 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
              ·
                convert haux0 a b c d (by positivity) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (3*a^3*b + a^3*d + 2*a^2*b^2 - 5*a^2*b*c + 4*a^2*b*d + a^2*c*d + 2*a^2*d^2 + a*b^3 + 4*a*b^2*c + a*b^2*d + a*b*c^2 - 24*a*b*c*d - 5*a*b*d^2 - 5*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 2*b^2*c^2 - 5*b^2*c*d + b*c^3 + 4*b*c^2*d + b*c*d^2 + 3*c^3*d + 2*c^2*d^2 + c*d^3) := by nlinarith only [hp]
  have hd : (0 : ℝ) < ((a + 2*b + c)*(a + c + 2*d)*(2*a + b + d)*(b + 2*c + d)) := by positivity
  have heqrat : ( (a - b) / (a + 2 * b + c) + (b - c) / (b + 2 * c + d) + (c - d) / (c + 2 * d + a) + (d - a) / (d + 2 * a + b) ) - ( 0  ) = (3*a^3*b + a^3*d + 2*a^2*b^2 - 5*a^2*b*c + 4*a^2*b*d + a^2*c*d + 2*a^2*d^2 + a*b^3 + 4*a*b^2*c + a*b^2*d + a*b*c^2 - 24*a*b*c*d - 5*a*b*d^2 - 5*a*c^2*d + 4*a*c*d^2 + 3*a*d^3 + 3*b^3*c + 2*b^2*c^2 - 5*b^2*c*d + b*c^3 + 4*b*c^2*d + b*c*d^2 + 3*c^3*d + 2*c^2*d^2 + c*d^3) / ((a + 2*b + c)*(a + c + 2*d)*(2*a + b + d)*(b + 2*c + d)) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a - b) / (a + 2 * b + c) + (b - c) / (b + 2 * c + d) + (c - d) / (c + 2 * d + a) + (d - a) / (d + 2 * a + b) ≥ 0) := @solution
#print axioms solution
