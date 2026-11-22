-- Prove2me | solution 1 for ShiShallow.padIn_castAdd
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:59:29.32469+00:00
-- url     : https://prove2.me/submissions/68286645-3aca-46b0-8cd9-d5c6339eb055

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

section
open ShiShallow

theorem solution {n m : ℕ} (x : Bits n) (i : Fin n) :
    padIn (m := m) x (Fin.castAdd m i) = x i := by simp [padIn]

end
