-- Prove2me | solution 1 for ShiShallow.apply1_eq_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:50:45.207885+00:00
-- url     : https://prove2.me/submissions/4e0673d5-f403-4834-be30-1490e61404d3

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

theorem solution {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n) :
    apply1 U i ψ = (apply1Matrix U i).mulVec ψ := by
  classical
  funext y
  have main : (apply1Matrix U i).mulVec ψ y
      = ∑ z ∈ Finset.univ.filter
          (fun z : Bits n => ∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k),
          U (y i) (z i) * ψ z := by
    unfold Matrix.mulVec dotProduct apply1Matrix
    simp only [Matrix.of_apply, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun z _ => by split <;> simp)
  have himg : Finset.univ.filter
        (fun z : Bits n => ∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k)
      = Finset.image (fun b : Bool => Function.update y i b) Finset.univ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨z i, ?_⟩
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · rw [Function.update_of_ne hk]; exact h k (by simpa using hk)
    · rintro ⟨b, -, rfl⟩ k hk
      exact (Function.update_of_ne (by simpa using hk) _ _).symm
  rw [main, himg, Finset.sum_image (by
        intro a _ b _ hab; simpa using congrFun hab i)]
  unfold apply1
  exact Finset.sum_congr rfl (fun b _ => by rw [Function.update_self])

end
