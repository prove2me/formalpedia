-- Prove2me | solution 1 for ShiShallow.cnotState_eq_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:51:52.790455+00:00
-- url     : https://prove2.me/submissions/ddc662b8-5b99-4bd0-b294-3d81d8b26c1f

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

theorem solution {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    cnotState i j hij ψ = (cnotMatrix i j).mulVec ψ := by
  classical
  funext y
  unfold Matrix.mulVec dotProduct cnotMatrix cnotState
  simp only [Matrix.of_apply]
  rw [Finset.sum_eq_single (Function.update y j (xor (y j) (y i)))]
  · rw [if_pos, one_mul]
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · have hkj : k ≠ j := by intro h; exact hk (by simp [h])
      exact (Function.update_of_ne hkj _ _).symm
    · exact Function.update_of_ne hij _ _
    · exact Function.update_self _ _ _
  · intro z _ hz
    rw [if_neg, zero_mul]
    rintro ⟨hoff, hi, hj⟩
    refine hz ?_
    funext k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self]; exact hj
    · rw [Function.update_of_ne hk]
      by_cases hki : k = i
      · subst hki; exact hi
      · exact (hoff k (by simp [hk, hki])).symm
  · intro h; exact absurd (Finset.mem_univ _) h

end
