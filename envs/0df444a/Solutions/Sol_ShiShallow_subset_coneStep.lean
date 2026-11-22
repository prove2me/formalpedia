-- Prove2me | solution 1 for ShiShallow.subset_coneStep
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:26:54.420419+00:00
-- url     : https://prove2.me/submissions/566f3fff-70b3-4fd6-9c33-4a191060b43b

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
import Definitions.Def_ShiShallow_Cone

section
open ShiShallow

theorem solution {n : ℕ} (l : List (Instr n)) (S : Finset (Fin n)) :
    S ⊆ coneStep l S := by
  induction l with
  | nil => exact fun a ha => ha
  | cons g t ih =>
      rw [coneStep_cons]
      split
      · exact fun a ha => Finset.mem_union_right _ (ih ha)
      · exact ih

end
