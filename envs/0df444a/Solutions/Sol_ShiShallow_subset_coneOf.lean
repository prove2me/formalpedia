-- Prove2me | solution 1 for ShiShallow.subset_coneOf
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:10:58.293323+00:00
-- url     : https://prove2.me/submissions/f9af5481-0b61-4e6f-b77a-0df34da83f3b

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
import Theorems.Thm_ShiShallow_subset_coneStep

section
open ShiShallow

theorem solution {n : ℕ} (c : Layered n) (S : Finset (Fin n)) : S ⊆ coneOf c S := by
  induction c with
  | nil => exact fun a ha => ha
  | cons l t ih =>
      rw [coneOf_cons]
      exact fun a ha => subset_coneStep l (coneOf t S) (ih ha)

end
