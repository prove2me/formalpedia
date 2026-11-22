-- Prove2me | solution 1 for ShiShallow.disjoint_coneStep
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:58:20.96581+00:00
-- url     : https://prove2.me/submissions/a4e1d83f-9d52-4db2-8180-c1bb6dd0744e

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

theorem solution {n : ℕ} {G : Finset (Fin n)} (l : List (Instr n)) (S : Finset (Fin n))
    (hS : Disjoint G S) (ht : ∀ g ∈ l, Disjoint G g.support) : Disjoint G (coneStep l S) := by
  induction l with
  | nil => rw [coneStep_nil]; exact hS
  | cons g t ih =>
    rw [coneStep_cons]
    have hrest : Disjoint G (coneStep t S) :=
      ih (fun h hh => ht h (List.mem_cons_of_mem _ hh))
    split
    · exact Finset.disjoint_union_right.2 ⟨ht g (by simp), hrest⟩
    · exact hrest

end
