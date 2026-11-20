-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TThresholdPolynomial_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:59:52.092029+00:00
-- url     : https://prove2.me/submissions/c981738d-e205-43bd-895c-323a3b09b909

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option autoImplicit false

theorem _root_.solution : 7 * ((1 - Real.sqrt (3 / 7 : Real)) / 2) ^ 2 - 7 * ((1 - Real.sqrt (3 / 7 : Real)) / 2) + 1 = 0 := by
  have hsqrt : Real.sqrt (3 / 7 : Real) ^ 2 = 3 / 7 :=
    Real.sq_sqrt (by norm_num)
  nlinarith [hsqrt]
