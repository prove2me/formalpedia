-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TRecurrence_lt_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:30:54.406669+00:00
-- url     : https://prove2.me/submissions/e7b3f6e3-192c-4282-bd0d-f769515889f6

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false

theorem _root_.solution (epsilon : Real) (hzero : 0 < epsilon) (hthreshold : epsilon < ((1 - Real.sqrt (3 / 7 : Real)) / 2)) : (let z : Real := (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6; let o : Real := ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6; z / (z + o)) < epsilon := by
  let theta : Real := ((1 - Real.sqrt (3 / 7 : Real)) / 2)
  change epsilon < theta at hthreshold
  have hsqrt_pos : 0 < Real.sqrt (3 / 7 : Real) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt (3 / 7 : Real) ^ 2 = 3 / 7 := Real.sq_sqrt (by norm_num)
  have hthetaHalf : theta < 1 / 2 := by
    dsimp [theta]
    linarith only [hsqrt_pos]
  have hthetaRoot : 7 * theta ^ 2 - 7 * theta + 1 = 0 := by
    dsimp [theta]
    nlinarith only [hsqrt_sq]
  have hfactor : 7 * epsilon ^ 2 - 7 * epsilon + 1 =
      (epsilon - theta) * (7 * epsilon + 7 * theta - 7) := by
    calc
      _ = (7 * epsilon ^ 2 - 7 * epsilon + 1) - (7 * theta ^ 2 - 7 * theta + 1) := by
        rw [hthetaRoot, sub_zero]
      _ = _ := by ring
  have hpolynomial : 0 < 7 * epsilon ^ 2 - 7 * epsilon + 1 := by
    rw [hfactor]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hthreshold) (by
      linarith only [hthreshold, hthetaHalf])
  have hepsilonHalf : epsilon < 1 / 2 := hthreshold.trans hthetaHalf
  have hcomplement : 0 < 1 - epsilon := by linarith only [hepsilonHalf]
  have hlinear : 0 < 1 - 2 * epsilon := by linarith only [hepsilonHalf]
  let z : Real := (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6
  let o : Real := ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6
  change z / (z + o) < epsilon
  have hz : 0 < z := by
    dsimp [z]
    positivity
  have ho : 0 < o := by
    dsimp [o]
    positivity
  apply (div_lt_iff₀ (add_pos hz ho)).2
  have hdiff : z - epsilon * (z + o) =
      -(epsilon * (1 - epsilon) * (1 - 2 * epsilon) * (7 * epsilon ^ 2 - 7 * epsilon + 1) / 6) := by
    dsimp [z, o]
    ring
  have hproduct : 0 < epsilon * (1 - epsilon) * (1 - 2 * epsilon) * (7 * epsilon ^ 2 - 7 * epsilon + 1) / 6 := by
    positivity
  linarith only [hdiff, hproduct]
