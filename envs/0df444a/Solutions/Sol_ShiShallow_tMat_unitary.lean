-- Prove2me | solution 1 for ShiShallow.tMat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:39:56.476033+00:00
-- url     : https://prove2.me/submissions/a43143a8-0177-4368-85fe-678392161f48

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

theorem solution : tMat.conjTranspose * tMat = 1 := by
  have key : (starRingEnd ℂ) (Complex.exp (Complex.I * Real.pi / 4))
      * Complex.exp (Complex.I * Real.pi / 4) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have : (starRingEnd ℂ) (Complex.I * Real.pi / 4) + Complex.I * Real.pi / 4 = 0 := by
      simp [map_div₀, map_mul, Complex.conj_I, map_ofNat]
      ring
    rw [this, Complex.exp_zero]
  ext a c
  cases a <;> cases c <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, tMat, Matrix.one_apply,
          Fintype.sum_bool, key]

end
