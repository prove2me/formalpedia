-- Prove2me | solution 1 for ShiShallow.conj_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:26:13.327376+00:00
-- url     : https://prove2.me/submissions/45329f6b-f425-4d01-88e0-fac6e5baa393

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

section
open ShiShallow

theorem solution {n : ℕ} (A X Y : Op n) :
    (X * Y).conjTranspose * A * (X * Y)
      = Y.conjTranspose * (X.conjTranspose * A * X) * Y := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end
