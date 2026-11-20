-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TRecurrence_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T12:18:35.000192+00:00
-- url     : https://prove2.me/submissions/3af245fd-9eef-49e7-b6ce-02fa8df01227

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
set_option autoImplicit false

theorem _root_.solution : (let epsilon : Real := (1 / 2 : Real); (let z : Real := (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6; let o : Real := ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6; z / (z + o))) = (1 / 2 : Real) := by
  norm_num
