-- Prove2me | solution 1 for ShiShallow.isLocal_gateMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:20:36.833813+00:00
-- url     : https://prove2.me/submissions/c9cac781-91f1-4182-8596-854249c8cdce

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
import Theorems.Thm_ShiShallow_isLocal_apply1Matrix
import Theorems.Thm_ShiShallow_isLocal_cnotMatrix

section
open ShiShallow

theorem solution {n : ℕ} (g : Instr n) : IsLocal g.support (gateMatrix g) := by
  cases g with
  | h i => exact isLocal_apply1Matrix hMat i
  | s i => exact isLocal_apply1Matrix sMat i
  | t i => exact isLocal_apply1Matrix tMat i
  | cnot i j hij => exact isLocal_cnotMatrix i j

end
