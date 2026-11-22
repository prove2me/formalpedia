-- Prove2me | solution 1 for ShiShallow.cnotMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:54:23.982638+00:00
-- url     : https://prove2.me/submissions/28b36eed-e0b3-491d-aced-b8c94b075d87

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

theorem solution {n : ℕ} (i j : Fin n) (hij : i ≠ j) (w v : Bits n) :
    cnotMatrix i j w v = if v = cnotEquiv i j hij w then 1 else 0 := by
  have hiff : ((∀ k, k ∉ ({i, j} : Finset (Fin n)) → w k = v k) ∧ v i = w i ∧
      v j = xor (w j) (w i)) ↔ v = cnotEquiv i j hij w := by
    simp only [cnotEquiv_apply]
    constructor
    · rintro ⟨hoff, hi, hj⟩
      funext k
      by_cases hk : k = j
      · subst hk; rw [Function.update_self]; exact hj
      · rw [Function.update_of_ne hk]
        by_cases hki : k = i
        · subst hki; exact hi
        · exact (hoff k (by simp [hk, hki])).symm
    · rintro rfl
      refine ⟨fun k hk => ?_, ?_, ?_⟩
      · have hkj : k ≠ j := fun h => hk (by simp [h])
        exact (Function.update_of_ne hkj _ _).symm
      · exact Function.update_of_ne hij _ _
      · exact Function.update_self _ _ _
  simp only [cnotMatrix, Matrix.of_apply, hiff]

end
