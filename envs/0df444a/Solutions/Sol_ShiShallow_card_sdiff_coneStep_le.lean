-- Prove2me | solution 1 for ShiShallow.card_sdiff_coneStep_le
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:32:25.764048+00:00
-- url     : https://prove2.me/submissions/24ceef77-9fbb-4a1e-9d04-a465c8854710

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
import Theorems.Thm_ShiShallow_card_sdiff_support_le_one

section
open ShiShallow

theorem solution {n : ℕ} (l : List (Instr n)) (S : Finset (Fin n)) :
    ((coneStep l S) \ S).card
      ≤ (l.filter (fun g => decide (g.support ∩ S).Nonempty)).length := by
  induction l with
  | nil => simp [coneStep_nil]
  | cons g t ih =>
      rw [coneStep_cons]
      by_cases h : (g.support ∩ S).Nonempty
      · rw [if_pos h, List.filter_cons_of_pos (by simpa using h), List.length_cons]
        have hsub : (g.support ∪ coneStep t S) \ S
            ⊆ (g.support \ S) ∪ (coneStep t S \ S) := by
          intro a ha
          rw [Finset.mem_sdiff, Finset.mem_union] at ha
          rcases ha.1 with h1 | h2
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h1, ha.2⟩)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h2, ha.2⟩)
        have h1 := card_sdiff_support_le_one g S h
        calc ((g.support ∪ coneStep t S) \ S).card
            ≤ ((g.support \ S) ∪ (coneStep t S \ S)).card := Finset.card_le_card hsub
          _ ≤ (g.support \ S).card + (coneStep t S \ S).card := Finset.card_union_le _ _
          _ ≤ 1 + (t.filter (fun g => decide (g.support ∩ S).Nonempty)).length := by
              have := ih; omega
          _ = (t.filter (fun g => decide (g.support ∩ S).Nonempty)).length + 1 := by omega
      · rw [if_neg h, List.filter_cons_of_neg (by simpa using h)]
        exact ih

end
