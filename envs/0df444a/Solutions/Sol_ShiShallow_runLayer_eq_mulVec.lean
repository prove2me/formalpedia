-- Prove2me | solution 1 for ShiShallow.runLayer_eq_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:38:17.461477+00:00
-- url     : https://prove2.me/submissions/db404967-636f-433f-8f61-cda070c03b00

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
import Theorems.Thm_ShiShallow_Instr_apply_eq_mulVec

section
open ShiShallow

theorem solution {n : ℕ} (l : List (Instr n)) (ψ : QState n) :
    runLayer l ψ = (layerMatrix l).mulVec ψ := by
  induction l generalizing ψ with
  | nil => rw [layerMatrix_nil, Matrix.one_mulVec]; rfl
  | cons g t ih =>
    show runLayer t (g.apply ψ) = _
    rw [ih, Instr.apply_eq_mulVec, layerMatrix_cons, Matrix.mulVec_mulVec]

end
