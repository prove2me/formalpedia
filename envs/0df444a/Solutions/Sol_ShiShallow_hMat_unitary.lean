-- Prove2me | solution 1 for ShiShallow.hMat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:16:17.679541+00:00
-- url     : https://prove2.me/submissions/fc8c9437-0770-45de-aac7-5ba228ebed6d

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
import Theorems.Thm_ShiShallow_inv_sqrt_two_mul_self

section
open ShiShallow

theorem solution : hMat.conjTranspose * hMat = 1 := by
  ext a c
  cases a <;> cases c <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hMat, Matrix.one_apply,
          Fintype.sum_bool, inv_sqrt_two_mul_self] <;>
    ring_nf <;> linear_combination inv_sqrt_two_mul_self

end
