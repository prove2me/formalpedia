-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TIteration_nonneg_and_lt_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:19:54.291738+00:00
-- url     : https://prove2.me/submissions/ac79c3d9-23ea-4ef8-8a45-ca5835c6779a

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false

theorem _root_.solution (epsilon : Real) (hzero : 0 <= epsilon)
    (hthreshold : epsilon < ((1 - Real.sqrt (3 / 7 : Real)) / 2)) (rounds : Nat) :
    let f : Real → Real := (fun input : Real =>
      let z : Real := (input ^ 5 + 5 * input ^ 2 * (1 - input) ^ 3) / 6
      let o : Real := ((1 - input) ^ 5 + 5 * input ^ 3 * (1 - input) ^ 2) / 6
      z / (z + o))
    0 <= Nat.iterate f rounds epsilon ∧ Nat.iterate f rounds epsilon < ((1 - Real.sqrt (3 / 7 : Real)) / 2) := by
  let f : Real → Real := (fun input : Real =>
      let z : Real := (input ^ 5 + 5 * input ^ 2 * (1 - input) ^ 3) / 6
      let o : Real := ((1 - input) ^ 5 + 5 * input ^ 3 * (1 - input) ^ 2) / 6
      z / (z + o))
  let theta : Real := ((1 - Real.sqrt (3 / 7 : Real)) / 2)
  change epsilon < theta at hthreshold
  change 0 <= Nat.iterate f rounds epsilon ∧ Nat.iterate f rounds epsilon < theta
  have hsqrt : 0 < Real.sqrt (3 / 7 : Real) := Real.sqrt_pos.2 (by norm_num)
  have hThetaUpper : theta < 1 / 2 := by
    dsimp [theta]
    linarith only [hsqrt]
  have hstep_nonneg (x : Real) (hx : 0 <= x) (hxthreshold : x < theta) : 0 <= f x := by
    have hxhalf : x < 1 / 2 := hxthreshold.trans hThetaUpper
    have hcomplement : 0 <= 1 - x := by linarith only [hxhalf]
    let z : Real := (x ^ 5 + 5 * x ^ 2 * (1 - x) ^ 3) / 6
    let o : Real := ((1 - x) ^ 5 + 5 * x ^ 3 * (1 - x) ^ 2) / 6
    change 0 <= z / (z + o)
    have hz : 0 <= z := by
      dsimp [z]
      positivity
    have ho : 0 <= o := by
      dsimp [o]
      positivity
    exact div_nonneg hz (add_nonneg hz ho)
  have hstep_zero : f 0 = 0 := by
    norm_num [f]
  have hstep_drop (x : Real) (hxpos : 0 < x) (hxthreshold : x < theta) : f x < x := by
    let theta : Real := ((1 - Real.sqrt (3 / 7 : Real)) / 2)
    change x < theta at hxthreshold
    have hsqrt_pos : 0 < Real.sqrt (3 / 7 : Real) := Real.sqrt_pos.2 (by norm_num)
    have hsqrt_sq : Real.sqrt (3 / 7 : Real) ^ 2 = 3 / 7 := Real.sq_sqrt (by norm_num)
    have hthetaHalf : theta < 1 / 2 := by
      dsimp [theta]
      linarith only [hsqrt_pos]
    have hthetaRoot : 7 * theta ^ 2 - 7 * theta + 1 = 0 := by
      dsimp [theta]
      nlinarith only [hsqrt_sq]
    have hfactor : 7 * x ^ 2 - 7 * x + 1 =
        (x - theta) * (7 * x + 7 * theta - 7) := by
      calc
        _ = (7 * x ^ 2 - 7 * x + 1) - (7 * theta ^ 2 - 7 * theta + 1) := by
          rw [hthetaRoot, sub_zero]
        _ = _ := by ring
    have hpolynomial : 0 < 7 * x ^ 2 - 7 * x + 1 := by
      rw [hfactor]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hxthreshold) (by
        linarith only [hxthreshold, hthetaHalf])
    have hepsilonHalf : x < 1 / 2 := hxthreshold.trans hthetaHalf
    have hcomplement : 0 < 1 - x := by linarith only [hepsilonHalf]
    have hlinear : 0 < 1 - 2 * x := by linarith only [hepsilonHalf]
    let z : Real := (x ^ 5 + 5 * x ^ 2 * (1 - x) ^ 3) / 6
    let o : Real := ((1 - x) ^ 5 + 5 * x ^ 3 * (1 - x) ^ 2) / 6
    change z / (z + o) < x
    have hz : 0 < z := by
      dsimp [z]
      positivity
    have ho : 0 < o := by
      dsimp [o]
      positivity
    apply (div_lt_iff₀ (add_pos hz ho)).2
    have hdiff : z - x * (z + o) =
        -(x * (1 - x) * (1 - 2 * x) * (7 * x ^ 2 - 7 * x + 1) / 6) := by
      dsimp [z, o]
      ring
    have hproduct : 0 < x * (1 - x) * (1 - 2 * x) * (7 * x ^ 2 - 7 * x + 1) / 6 := by
      positivity
    linarith only [hdiff, hproduct]
  have hstep_lt (x : Real) (hx : 0 <= x) (hxthreshold : x < theta) : f x < theta := by
    rcases eq_or_lt_of_le hx with heq | hpos
    · subst x
      rw [hstep_zero]
      exact hxthreshold
    · exact (hstep_drop x hpos hxthreshold).trans hxthreshold
  induction rounds with
  | zero =>
    simpa only [Function.iterate_zero_apply] using And.intro hzero hthreshold
  | succ n ih =>
    let x := Nat.iterate f n epsilon
    have hx : 0 <= x := ih.1
    have hxthreshold : x < theta := ih.2
    simpa only [Function.iterate_succ_apply'] using
      And.intro (hstep_nonneg x hx hxthreshold) (hstep_lt x hx hxthreshold)
