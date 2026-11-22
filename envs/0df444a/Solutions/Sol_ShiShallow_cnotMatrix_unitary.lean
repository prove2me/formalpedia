-- Prove2me | solution 1 for ShiShallow.cnotMatrix_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:23:33.928983+00:00
-- url     : https://prove2.me/submissions/da180319-47de-4b19-a80f-b0d3e1f53d7b

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
import Theorems.Thm_ShiShallow_cnotMatrix_apply

section
open ShiShallow

theorem solution {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (cnotMatrix i j).conjTranspose * cnotMatrix i j = 1 := by
  classical
  ext y z
  have hentry : ((cnotMatrix i j).conjTranspose * cnotMatrix i j) y z
      = ∑ w : Bits n, (starRingEnd ℂ) (cnotMatrix i j w y) * cnotMatrix i j w z := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hentry]
  simp only [cnotMatrix_apply i j hij, apply_ite (starRingEnd ℂ), map_one, map_zero]
  rw [Finset.sum_eq_single ((cnotEquiv i j hij).symm y)]
  · rw [Equiv.apply_symm_apply, if_pos rfl, one_mul, Matrix.one_apply]
    by_cases h : y = z
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro w _ hw
    rw [if_neg (fun hc => hw (by rw [hc, Equiv.symm_apply_apply])), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end
