-- Prove2me | solution 1 for ShiShallow.card_sdiff_support_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:12:13.572243+00:00
-- url     : https://prove2.me/submissions/b9f31323-c91a-4635-9592-592c2f0f8d02

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
import Theorems.Thm_ShiShallow_card_support_le_two

section
open ShiShallow

theorem solution {n : ℕ} (g : Instr n) (S : Finset (Fin n))
    (h : (g.support ∩ S).Nonempty) : (g.support \ S).card ≤ 1 := by
  obtain ⟨a, ha⟩ := h
  rw [Finset.mem_inter] at ha
  have hsub : g.support \ S ⊆ g.support.erase a := by
    intro b hb
    rw [Finset.mem_sdiff] at hb
    refine Finset.mem_erase.mpr ⟨?_, hb.1⟩
    intro hba
    exact hb.2 (hba ▸ ha.2)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem ha.1] at hcard
  have h2 := card_support_le_two g
  omega

end
