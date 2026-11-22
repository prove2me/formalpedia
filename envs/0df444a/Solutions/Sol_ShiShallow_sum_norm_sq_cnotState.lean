-- Prove2me | solution 1 for ShiShallow.sum_norm_sq_cnotState
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:33:02.194091+00:00
-- url     : https://prove2.me/submissions/3592c41a-6853-4fca-be59-d44f63c0301f

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

section
open ShiShallow

theorem solution {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    ∑ x : Bits n, ‖cnotState i j hij ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := Fintype.sum_equiv (cnotEquiv i j hij) _ _ (fun _ => rfl)

end
