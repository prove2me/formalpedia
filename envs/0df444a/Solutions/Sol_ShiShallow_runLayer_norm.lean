-- Prove2me | solution 1 for ShiShallow.runLayer_norm
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:54:12.290983+00:00
-- url     : https://prove2.me/submissions/1ecebb0c-e56b-4bf2-a441-bff68019020a

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
import Theorems.Thm_ShiShallow_Instr_apply_norm

section
open ShiShallow

theorem solution {n : ℕ} (l : List (Instr n)) (ψ : QState n) :
    ∑ x : Bits n, ‖runLayer l ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by
  induction l generalizing ψ with
  | nil => rfl
  | cons g t ih => exact (ih (g.apply ψ)).trans (Instr.apply_norm g ψ)

end
