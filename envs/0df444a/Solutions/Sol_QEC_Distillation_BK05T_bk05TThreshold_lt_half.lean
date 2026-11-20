-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TThreshold_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:59:45.808927+00:00
-- url     : https://prove2.me/submissions/d73809ea-d102-412e-8b78-bfb3a09d0a13

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option autoImplicit false

theorem _root_.solution : ((1 - Real.sqrt (3 / 7 : Real)) / 2) < 1 / 2 := by
  have hsqrt_pos : 0 < Real.sqrt (3 / 7 : Real) :=
    Real.sqrt_pos.2 (by norm_num)
  linarith
