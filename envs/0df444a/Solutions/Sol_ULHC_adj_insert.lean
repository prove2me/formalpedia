-- Prove2me | solution 1 for ULHC.adj_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:55.634241+00:00
-- url     : https://prove2.me/submissions/22a5d057-e8db-4adb-a6a8-114fe27e3a6b

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Conn_symm


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {e : Edge} {a b : Pt} :
    Adj (insert e F) a b ↔ Adj F a b ∨ (a = e.p ∧ b = e.q) ∨ (a = e.q ∧ b = e.p) := by
  constructor
  · rintro ⟨f, hf, h⟩
    rcases Finset.mem_insert.1 hf with hf | hf
    · subst hf; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1.symm, h2.symm⟩)
      · exact Or.inr (Or.inr ⟨h2.symm, h1.symm⟩)
    · exact Or.inl ⟨f, hf, h⟩
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono (Finset.subset_insert _ _)
    · exact ⟨e, Finset.mem_insert_self _ _, Or.inl ⟨h1.symm, h2.symm⟩⟩
    · exact ⟨e, Finset.mem_insert_self _ _, Or.inr ⟨h2.symm, h1.symm⟩⟩
end ULHC
