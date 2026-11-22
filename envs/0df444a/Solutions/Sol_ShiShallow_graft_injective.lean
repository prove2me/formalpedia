-- Prove2me | solution 1 for ShiShallow.graft_injective
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:43:19.538706+00:00
-- url     : https://prove2.me/submissions/970b0667-230a-42ee-bfe5-b247d0aff62a

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

theorem solution {n : ℕ} (S : Finset (Fin n)) (v : Bits n) :
    Function.Injective (graft S v) := by
  intro w w' hw
  funext k
  have hk := congrFun hw k.1
  rw [graft_of_mem S v w k.2, graft_of_mem S v w' k.2] at hk
  simpa using hk

end
