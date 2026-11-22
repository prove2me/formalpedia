-- Prove2me | solution 1 for ShiShallow.isLocal_conj
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:48:59.022994+00:00
-- url     : https://prove2.me/submissions/2292f15f-ff85-45ac-8f06-9ee9a6f7f17a

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
import Theorems.Thm_ShiShallow_IsLocal_mul

section
open ShiShallow

theorem solution {n : ℕ} {T G : Finset (Fin n)} {A V : Op n}
    (hA : IsLocal T A) (hV : IsLocal G V) :
    IsLocal (G ∪ T) (V.conjTranspose * A * V) := by
  have h2 : IsLocal ((G ∪ T) ∪ G) (V.conjTranspose * A * V) :=
    (hV.conjTranspose.mul hA).mul hV
  have heq : ((G ∪ T) ∪ G) = G ∪ T := by
    ext k; simp only [Finset.mem_union]; tauto
  rwa [heq] at h2

end
