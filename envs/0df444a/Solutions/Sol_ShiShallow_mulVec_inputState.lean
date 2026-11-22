-- Prove2me | solution 1 for ShiShallow.mulVec_inputState
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:39:40.83971+00:00
-- url     : https://prove2.me/submissions/fd374f02-07a9-46e2-bccb-cc39b8a5708d

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
import Theorems.Thm_ShiShallow_inputState_eq_indicator

section
open ShiShallow

theorem solution {n m : ℕ} (A : Op (n + m)) (x : Bits n) (y : Bits (n + m)) :
    A.mulVec (inputState x) y = A y (padIn x) := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single (padIn x)]
  · rw [inputState_eq_indicator, if_pos rfl, mul_one]
  · intro z _ hz
    rw [inputState_eq_indicator, if_neg hz, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end
