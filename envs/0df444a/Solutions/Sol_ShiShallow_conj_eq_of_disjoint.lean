-- Prove2me | solution 1 for ShiShallow.conj_eq_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:24:49.519747+00:00
-- url     : https://prove2.me/submissions/0979e02e-780a-4798-8d91-49c6b25cb385

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
import Theorems.Thm_ShiShallow_IsLocal_conjTranspose
import Theorems.Thm_ShiShallow_mul_comm_of_disjoint

section
open ShiShallow

theorem solution {n : ℕ} {G T : Finset (Fin n)} {A V : Op n}
    (hA : IsLocal T A) (hV : IsLocal G V) (hd : Disjoint G T)
    (hVu : V.conjTranspose * V = 1) : V.conjTranspose * A * V = A := by
  rw [Matrix.mul_assoc, mul_comm_of_disjoint hA hV hd, ← Matrix.mul_assoc, hVu, Matrix.one_mul]

end
