-- Prove2me | solution 1 for ShiShallow.Instr.apply_norm
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:47:26.423278+00:00
-- url     : https://prove2.me/submissions/e5115b47-cdbf-4c83-86f1-520831990897

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
import Theorems.Thm_ShiShallow_hMat_unitary
import Theorems.Thm_ShiShallow_sMat_unitary
import Theorems.Thm_ShiShallow_sum_norm_sq_apply1
import Theorems.Thm_ShiShallow_sum_norm_sq_cnotState
import Theorems.Thm_ShiShallow_tMat_unitary

section
open ShiShallow

theorem solution {n : ℕ} (g : Instr n) (ψ : QState n) :
    ∑ x : Bits n, ‖g.apply ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by
  cases g with
  | h i => exact sum_norm_sq_apply1 hMat_unitary i ψ
  | s i => exact sum_norm_sq_apply1 sMat_unitary i ψ
  | t i => exact sum_norm_sq_apply1 tMat_unitary i ψ
  | cnot i j hij => exact sum_norm_sq_cnotState i j hij ψ

end
