-- Prove2me | solution 1 for ShiShallow.sum_of_vanishing_single
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:52:59.831634+00:00
-- url     : https://prove2.me/submissions/a48dd751-7baf-46d0-971a-9699b1521a05

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

theorem solution {n : ℕ} (i : Fin n) (y : Bits n) (G : Bits n → ℂ)
    (hG : ∀ w : Bits n, (¬ ∀ k, k ∉ ({i} : Finset (Fin n)) → w k = y k) → G w = 0) :
    ∑ w : Bits n, G w = ∑ b : Bool, G (Function.update y i b) := by
  classical
  have himg : ∑ b : Bool, G (Function.update y i b)
      = ∑ w ∈ Finset.image (fun b : Bool => Function.update y i b) Finset.univ, G w :=
    (Finset.sum_image (fun a _ b _ hab => by simpa using congrFun hab i)).symm
  rw [himg]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro w _ hw
  refine hG w ?_
  intro hagree
  refine hw (Finset.mem_image.2 ⟨w i, Finset.mem_univ _, ?_⟩)
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · rw [Function.update_of_ne hk]; exact (hagree k (by simpa using hk)).symm

end
