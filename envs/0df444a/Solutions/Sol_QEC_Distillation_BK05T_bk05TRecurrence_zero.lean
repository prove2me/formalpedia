-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TRecurrence_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:28:24.382174+00:00
-- url     : https://prove2.me/submissions/2f0402df-f88b-42b1-b4a6-031856718a92

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
set_option autoImplicit false

theorem _root_.solution : (let epsilon : Real := 0; (let z : Real := (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6; let o : Real := ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6; z / (z + o))) = 0 := by
  norm_num
