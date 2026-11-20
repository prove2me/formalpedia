-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TIteration_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:44:12.859284+00:00
-- url     : https://prove2.me/submissions/ba2434b5-c684-479c-bf37-ba85cb424642

import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false

theorem _root_.solution (epsilon : Real) :
  Nat.iterate (fun input : Real =>
      let z : Real := (input ^ 5 + 5 * input ^ 2 * (1 - input) ^ 3) / 6
      let o : Real := ((1 - input) ^ 5 + 5 * input ^ 3 * (1 - input) ^ 2) / 6
      z / (z + o)) 0 epsilon = epsilon := rfl
