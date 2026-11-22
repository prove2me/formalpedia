-- Prove2me | solution 1 for ShiShallow.padIn_natAdd
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:00:45.975211+00:00
-- url     : https://prove2.me/submissions/484a8270-8900-48ea-9d10-01eaa8aa0846

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

theorem solution {n m : ℕ} (x : Bits n) (j : Fin m) :
    padIn (m := m) x (Fin.natAdd n j) = false := by simp [padIn]

end
