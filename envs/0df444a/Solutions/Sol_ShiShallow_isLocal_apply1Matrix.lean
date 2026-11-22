-- Prove2me | solution 1 for ShiShallow.isLocal_apply1Matrix
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:47:49.442127+00:00
-- url     : https://prove2.me/submissions/b57422fb-091c-4089-a756-3e5f67bb38bc

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

theorem solution {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) :
    IsLocal {i} (apply1Matrix U i) := by
  refine ⟨fun y z hne => by simp only [apply1Matrix, Matrix.of_apply, if_neg hne],
    fun y z y' z' hy hz hyz hyz' => ?_⟩
  have hi : i ∈ ({i} : Finset (Fin n)) := Finset.mem_singleton_self i
  simp only [apply1Matrix, Matrix.of_apply, if_pos hyz, if_pos hyz', hy i hi, hz i hi]

end
