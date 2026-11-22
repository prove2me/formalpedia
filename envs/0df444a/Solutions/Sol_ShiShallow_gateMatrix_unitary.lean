-- Prove2me | solution 1 for ShiShallow.gateMatrix_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:35:13.410909+00:00
-- url     : https://prove2.me/submissions/1d1f7b61-b33a-407c-8dac-88a60df005e3

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
import Theorems.Thm_ShiShallow_apply1Matrix_unitary
import Theorems.Thm_ShiShallow_cnotMatrix_unitary
import Theorems.Thm_ShiShallow_hMat_unitary
import Theorems.Thm_ShiShallow_sMat_unitary
import Theorems.Thm_ShiShallow_tMat_unitary

section
open ShiShallow

theorem solution {n : ℕ} (g : Instr n) : (gateMatrix g).conjTranspose * gateMatrix g = 1 := by
  cases g with
  | h i => exact apply1Matrix_unitary hMat_unitary i
  | s i => exact apply1Matrix_unitary sMat_unitary i
  | t i => exact apply1Matrix_unitary tMat_unitary i
  | cnot i j hij => exact cnotMatrix_unitary i j hij

end
