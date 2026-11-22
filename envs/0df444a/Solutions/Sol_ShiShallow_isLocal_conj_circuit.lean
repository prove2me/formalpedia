-- Prove2me | solution 1 for ShiShallow.isLocal_conj_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:59:35.456765+00:00
-- url     : https://prove2.me/submissions/49b76410-d073-4296-9614-104c5ec87fb6

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
import Definitions.Def_ShiShallow_Cone
import Definitions.Def_ShiShallow_Operator
import Theorems.Thm_ShiShallow_IsLocal_conjTranspose
import Theorems.Thm_ShiShallow_conj_mul_eq
import Theorems.Thm_ShiShallow_isLocal_conj_layer

section
open ShiShallow

theorem solution {n : ℕ} (c : Layered n) (hc : ∀ l ∈ c, LayerOk l)
    {S : Finset (Fin n)} {A : Op n} (hA : IsLocal S A) :
    IsLocal (coneOf c S) ((circMatrix c).conjTranspose * A * circMatrix c) := by
  induction c with
  | nil =>
    rw [circMatrix_nil, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, coneOf_nil]
    exact hA
  | cons l t ih =>
    have hinner := ih (fun m hm => hc m (List.mem_cons_of_mem _ hm))
    rw [circMatrix_cons, conj_mul_eq, coneOf_cons]
    exact isLocal_conj_layer l (hc l (by simp)) hinner

end
