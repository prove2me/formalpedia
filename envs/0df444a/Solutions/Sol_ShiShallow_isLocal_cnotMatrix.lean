-- Prove2me | solution 1 for ShiShallow.isLocal_cnotMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:49:13.271585+00:00
-- url     : https://prove2.me/submissions/c76e9804-0187-487b-8e0e-4f63b91be38b

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

theorem solution {n : ℕ} (i j : Fin n) :
    IsLocal {i, j} (cnotMatrix i j) := by
  have hi : i ∈ ({i, j} : Finset (Fin n)) := Finset.mem_insert_self i {j}
  have hj : j ∈ ({i, j} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
  refine ⟨fun y z hne => ?_, fun y z y' z' hy hz hyz hyz' => ?_⟩
  · simp only [cnotMatrix, Matrix.of_apply]
    exact if_neg (fun hc => hne hc.1)
  · simp only [cnotMatrix, Matrix.of_apply, hy i hi, hy j hj, hz i hi, hz j hj,
      iff_of_true hyz hyz']

end
