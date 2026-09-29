-- Prove2me | solution 1 for WorkbookSource.base_26997
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T08:12:31.434534+00:00
-- url     : https://prove2.me/submissions/50b136de-5352-406c-95b4-b21de6ab2253

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b + c + d) * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) ≥ 4 * a * b * c * d * (b / a + c / b + d / c + a / d)  := by
  have haux0 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) (hord3 : c ≤ d) : 0 ≤ (a^4 + a^3*b + a^3*c + a^3*d - 4*a^2*b*c + a*b^3 - 4*a*b*d^2 + a*c^3 - 4*a*c^2*d + a*d^3 + b^4 + b^3*c + b^3*d - 4*b^2*c*d + b*c^3 + b*d^3 + c^4 + c^3*d + c*d^3 + d^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hdiff3 : 0 ≤ (d - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((b - a))*(11*((b - a)) + 16*((c - b)) + 6*((d - c))) + ((c - b))*(16*((c - b)) + 16*((d - c))) + 11*((d - c))^2) + ((b - a))*(((b - a))*(15*((b - a)) + 34*((c - b)) + 15*((d - c))) + ((c - b))*(42*((c - b)) + 42*((d - c))) + 23*((d - c))^2) + ((c - b))*(((c - b))*(16*((c - b)) + 26*((d - c))) + 24*((d - c))^2) + 7*((d - c))^3) + ((b - a))*(((b - a))*(((b - a))*(5*((b - a)) + 16*((c - b)) + 8*((d - c))) + ((c - b))*(26*((c - b)) + 26*((d - c))) + 12*((d - c))^2) + ((c - b))*(((c - b))*(18*((c - b)) + 27*((d - c))) + 21*((d - c))^2) + 6*((d - c))^3) + ((c - b))*(((c - b))*(((c - b))*(4*((c - b)) + 8*((d - c))) + 9*((d - c))^2) + 5*((d - c))^3) + ((d - c))^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ d) (hord3 : d ≤ c) : 0 ≤ (a^4 + a^3*b + a^3*c + a^3*d - 4*a^2*b*c + a*b^3 - 4*a*b*d^2 + a*c^3 - 4*a*c^2*d + a*d^3 + b^4 + b^3*c + b^3*d - 4*b^2*c*d + b*c^3 + b*d^3 + c^4 + c^3*d + c*d^3 + d^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (d - b) := by linarith
    have hdiff3 : 0 ≤ (c - d) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((b - a))*(11*((b - a)) + 16*((d - b)) + 10*((c - d))) + ((d - b))*(16*((d - b)) + 16*((c - d))) + 11*((c - d))^2) + ((b - a))*(((b - a))*(15*((b - a)) + 34*((d - b)) + 19*((c - d))) + ((d - b))*(42*((d - b)) + 42*((c - d))) + 23*((c - d))^2) + ((d - b))*(((d - b))*(16*((d - b)) + 22*((c - d))) + 20*((c - d))^2) + 7*((c - d))^3) + ((b - a))*(((b - a))*(((b - a))*(5*((b - a)) + 16*((d - b)) + 8*((c - d))) + ((d - b))*(26*((d - b)) + 26*((c - d))) + 12*((c - d))^2) + ((d - b))*(((d - b))*(18*((d - b)) + 27*((c - d))) + 21*((c - d))^2) + 6*((c - d))^3) + ((d - b))*(((d - b))*(((d - b))*(4*((d - b)) + 8*((c - d))) + 9*((c - d))^2) + 5*((c - d))^3) + ((c - d))^4 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) (hord3 : b ≤ d) : 0 ≤ (a^4 + a^3*b + a^3*c + a^3*d - 4*a^2*b*c + a*b^3 - 4*a*b*d^2 + a*c^3 - 4*a*c^2*d + a*d^3 + b^4 + b^3*c + b^3*d - 4*b^2*c*d + b*c^3 + b*d^3 + c^4 + c^3*d + c*d^3 + d^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hdiff3 : 0 ≤ (d - b) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((c - a))*(11*((c - a)) + 12*((b - c)) + 6*((d - b))) + ((b - c))*(12*((b - c)) + 12*((d - b))) + 11*((d - b))^2) + ((c - a))*(((c - a))*(15*((c - a)) + 26*((b - c)) + 15*((d - b))) + ((b - c))*(30*((b - c)) + 34*((d - b))) + 23*((d - b))^2) + ((b - c))*(((b - c))*(12*((b - c)) + 18*((d - b))) + 20*((d - b))^2) + 7*((d - b))^3) + ((c - a))*(((c - a))*(((c - a))*(5*((c - a)) + 12*((b - c)) + 8*((d - b))) + ((b - c))*(18*((b - c)) + 22*((d - b))) + 12*((d - b))^2) + ((b - c))*(((b - c))*(14*((b - c)) + 23*((d - b))) + 21*((d - b))^2) + 6*((d - b))^3) + ((b - c))*(((b - c))*(((b - c))*(4*((b - c)) + 8*((d - b))) + 9*((d - b))^2) + 5*((d - b))^3) + ((d - b))^4 := by positivity
    convert hpos using 1 <;> ring
  have haux3 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ d) (hord3 : d ≤ b) : 0 ≤ (a^4 + a^3*b + a^3*c + a^3*d - 4*a^2*b*c + a*b^3 - 4*a*b*d^2 + a*c^3 - 4*a*c^2*d + a*d^3 + b^4 + b^3*c + b^3*d - 4*b^2*c*d + b*c^3 + b*d^3 + c^4 + c^3*d + c*d^3 + d^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (d - c) := by linarith
    have hdiff3 : 0 ≤ (b - d) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((c - a))*(11*((c - a)) + 12*((d - c)) + 6*((b - d))) + ((d - c))*(12*((d - c)) + 12*((b - d))) + 11*((b - d))^2) + ((c - a))*(((c - a))*(15*((c - a)) + 26*((d - c)) + 11*((b - d))) + ((d - c))*(30*((d - c)) + 26*((b - d))) + 19*((b - d))^2) + ((d - c))*(((d - c))*(12*((d - c)) + 18*((b - d))) + 20*((b - d))^2) + 7*((b - d))^3) + ((c - a))*(((c - a))*(((c - a))*(5*((c - a)) + 12*((d - c)) + 4*((b - d))) + ((d - c))*(18*((d - c)) + 14*((b - d))) + 8*((b - d))^2) + ((d - c))*(((d - c))*(14*((d - c)) + 19*((b - d))) + 17*((b - d))^2) + 6*((b - d))^3) + ((d - c))*(((d - c))*(((d - c))*(4*((d - c)) + 8*((b - d))) + 9*((b - d))^2) + 5*((b - d))^3) + ((b - d))^4 := by positivity
    convert hpos using 1 <;> ring
  have haux4 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ d) (hord2 : d ≤ b) (hord3 : b ≤ c) : 0 ≤ (a^4 + a^3*b + a^3*c + a^3*d - 4*a^2*b*c + a*b^3 - 4*a*b*d^2 + a*c^3 - 4*a*c^2*d + a*d^3 + b^4 + b^3*c + b^3*d - 4*b^2*c*d + b*c^3 + b*d^3 + c^4 + c^3*d + c*d^3 + d^4) := by
    have hdiff1 : 0 ≤ (d - a) := by linarith
    have hdiff2 : 0 ≤ (b - d) := by linarith
    have hdiff3 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((d - a))*(11*((d - a)) + 16*((b - d)) + 10*((c - b))) + ((b - d))*(16*((b - d)) + 16*((c - b))) + 11*((c - b))^2) + ((d - a))*(((d - a))*(15*((d - a)) + 30*((b - d)) + 19*((c - b))) + ((b - d))*(38*((b - d)) + 42*((c - b))) + 23*((c - b))^2) + ((b - d))*(((b - d))*(16*((b - d)) + 26*((c - b))) + 24*((c - b))^2) + 7*((c - b))^3) + ((d - a))*(((d - a))*(((d - a))*(5*((d - a)) + 12*((b - d)) + 8*((c - b))) + ((b - d))*(18*((b - d)) + 22*((c - b))) + 12*((c - b))^2) + ((b - d))*(((b - d))*(14*((b - d)) + 23*((c - b))) + 21*((c - b))^2) + 6*((c - b))^3) + ((b - d))*(((b - d))*(((b - d))*(4*((b - d)) + 8*((c - b))) + 9*((c - b))^2) + 5*((c - b))^3) + ((c - b))^4 := by positivity
    convert hpos using 1 <;> ring
  have haux5 (a b c d : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ d) (hord2 : d ≤ c) (hord3 : c ≤ b) : 0 ≤ (a^4 + a^3*b + a^3*c + a^3*d - 4*a^2*b*c + a*b^3 - 4*a*b*d^2 + a*c^3 - 4*a*c^2*d + a*d^3 + b^4 + b^3*c + b^3*d - 4*b^2*c*d + b*c^3 + b*d^3 + c^4 + c^3*d + c*d^3 + d^4) := by
    have hdiff1 : 0 ≤ (d - a) := by linarith
    have hdiff2 : 0 ≤ (c - d) := by linarith
    have hdiff3 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (a)*((a)*(((d - a))*(11*((d - a)) + 16*((c - d)) + 6*((b - c))) + ((c - d))*(16*((c - d)) + 16*((b - c))) + 11*((b - c))^2) + ((d - a))*(((d - a))*(15*((d - a)) + 30*((c - d)) + 11*((b - c))) + ((c - d))*(38*((c - d)) + 34*((b - c))) + 19*((b - c))^2) + ((c - d))*(((c - d))*(16*((c - d)) + 22*((b - c))) + 20*((b - c))^2) + 7*((b - c))^3) + ((d - a))*(((d - a))*(((d - a))*(5*((d - a)) + 12*((c - d)) + 4*((b - c))) + ((c - d))*(18*((c - d)) + 14*((b - c))) + 8*((b - c))^2) + ((c - d))*(((c - d))*(14*((c - d)) + 19*((b - c))) + 17*((b - c))^2) + 6*((b - c))^3) + ((c - d))*(((c - d))*(((c - d))*(4*((c - d)) + 8*((b - c))) + 9*((b - c))^2) + 5*((b - c))^3) + ((b - c))^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4 + a^3*b + a^3*c + a^3*d - 4*a^2*b*c + a*b^3 - 4*a*b*d^2 + a*c^3 - 4*a*c^2*d + a*d^3 + b^4 + b^3*c + b^3*d - 4*b^2*c*d + b*c^3 + b*d^3 + c^4 + c^3*d + c*d^3 + d^4) := by
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
  have hn : 0 ≤ (a^4 + a^3*b + a^3*c + a^3*d - 4*a^2*b*c + a*b^3 - 4*a*b*d^2 + a*c^3 - 4*a*c^2*d + a*d^3 + b^4 + b^3*c + b^3*d - 4*b^2*c*d + b*c^3 + b*d^3 + c^4 + c^3*d + c*d^3 + d^4) := by nlinarith only [hp]
  have hd : (0 : ℝ) < (1) := by positivity
  have heqrat : ( (a + b + c + d) * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) ) - ( 4 * a * b * c * d * (b / a + c / b + d / c + a / d)  ) = (a^4 + a^3*b + a^3*c + a^3*d - 4*a^2*b*c + a*b^3 - 4*a*b*d^2 + a*c^3 - 4*a*c^2*d + a*d^3 + b^4 + b^3*c + b^3*d - 4*b^2*c*d + b*c^3 + b*d^3 + c^4 + c^3*d + c*d^3 + d^4) / (1) := by
    field_simp (disch := positivity)
    <;> ring
  have hfrac := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hfrac]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), (a + b + c + d) * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) ≥ 4 * a * b * c * d * (b / a + c / b + d / c + a / d)) := @solution
#print axioms solution
