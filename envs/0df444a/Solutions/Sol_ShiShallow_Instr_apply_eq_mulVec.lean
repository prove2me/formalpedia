-- Prove2me | solution 1 for ShiShallow.Instr.apply_eq_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:18:48.370135+00:00
-- url     : https://prove2.me/submissions/a2e98d11-909a-45b3-96d2-21d97f9f8007

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the target theorem is renamed to `solution`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit
import Definitions.Def_ShiShallow_Operator
import Theorems.Thm_ShiShallow_apply1_eq_mulVec
import Theorems.Thm_ShiShallow_cnotState_eq_mulVec

section
open ShiShallow

theorem solution {n : ℕ} (g : Instr n) (ψ : QState n) :
    g.apply ψ = (gateMatrix g).mulVec ψ := by
  cases g with
  | h i => exact apply1_eq_mulVec hMat i ψ
  | s i => exact apply1_eq_mulVec sMat i ψ
  | t i => exact apply1_eq_mulVec tMat i ψ
  | cnot i j hij => exact cnotState_eq_mulVec i j hij ψ

end
