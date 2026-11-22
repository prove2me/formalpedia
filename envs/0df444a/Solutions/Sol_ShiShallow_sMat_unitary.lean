-- Prove2me | solution 1 for ShiShallow.sMat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:38:32.326598+00:00
-- url     : https://prove2.me/submissions/6800b5a2-d8e7-46f3-957b-3fc6aeeec9fa

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

theorem solution : sMat.conjTranspose * sMat = 1 := by
  ext a c
  cases a <;> cases c <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, sMat, Matrix.one_apply,
          Fintype.sum_bool, Complex.conj_I] <;> ring_nf <;> simp [Complex.I_mul_I]

end
