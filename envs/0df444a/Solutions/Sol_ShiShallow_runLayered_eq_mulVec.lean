-- Prove2me | solution 1 for ShiShallow.runLayered_eq_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:50:22.808672+00:00
-- url     : https://prove2.me/submissions/62e4430d-78b0-42e6-a782-abdcc292ae25

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
import Theorems.Thm_ShiShallow_runLayer_eq_mulVec

section
open ShiShallow

theorem solution {n : ℕ} (c : Layered n) (ψ : QState n) :
    runLayered c ψ = (circMatrix c).mulVec ψ := by
  induction c generalizing ψ with
  | nil => rw [circMatrix_nil, Matrix.one_mulVec]; rfl
  | cons l t ih =>
    show runLayered t (runLayer l ψ) = _
    rw [ih, runLayer_eq_mulVec, circMatrix_cons, Matrix.mulVec_mulVec]

end
