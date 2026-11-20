-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TThresholdPolynomial_pos_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:28:27.927638+00:00
-- url     : https://prove2.me/submissions/c2926a38-dad9-4266-bc3c-2f52f201d992

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false

theorem _root_.solution (epsilon : Real) (hepsilon : epsilon < ((1 - Real.sqrt (3 / 7 : Real)) / 2)) : 0 < 7 * epsilon ^ 2 - 7 * epsilon + 1 := by
  let theta : Real := ((1 - Real.sqrt (3 / 7 : Real)) / 2)
  change epsilon < theta at hepsilon
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
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hepsilon) (by
      linarith only [hepsilon, hthetaHalf])
  exact hpolynomial
