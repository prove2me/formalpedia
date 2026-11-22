-- Prove2me | solution 1 for ShiShallow.sum_of_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:17:33.006288+00:00
-- url     : https://prove2.me/submissions/f9e77ddb-10b7-4a14-a4c6-d02b35d76ece

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
import Theorems.Thm_ShiShallow_graft_injective

section
open ShiShallow

theorem solution {n : ℕ} (S : Finset (Fin n)) (v : Bits n) (F : Bits n → ℂ)
    (hF : ∀ u : Bits n, (¬ ∀ k, k ∉ S → u k = v k) → F u = 0) :
    ∑ u : Bits n, F u = ∑ w : {k : Fin n // k ∈ S} → Bool, F (graft S v w) := by
  classical
  have himg : ∑ w : {k : Fin n // k ∈ S} → Bool, F (graft S v w)
      = ∑ u ∈ Finset.image (graft S v) Finset.univ, F u :=
    (Finset.sum_image (fun a _ b _ h => graft_injective S v h)).symm
  rw [himg]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro u _ hu
  refine hF u ?_
  intro hagree
  refine hu (Finset.mem_image.2 ⟨fun k => u k.1, Finset.mem_univ _, ?_⟩)
  funext k
  by_cases hk : k ∈ S
  · rw [graft_of_mem S v _ hk]
  · rw [graft_of_not_mem S v _ hk]; exact (hagree k hk).symm

end
