-- Prove2me | solution 1 for ULHC.conn_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:35.959699+00:00
-- url     : https://prove2.me/submissions/cf040875-e225-4ae2-99b3-480c484aa628

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_adj_insert
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Conn_of_adj
import Theorems.Thm_ULHC_Conn_of_edge
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {e : Edge} {x y : Pt} :
    Conn (insert e F) x y ↔
      Conn F x y ∨ (Conn F x e.p ∧ Conn F e.q y) ∨ (Conn F x e.q ∧ Conn F e.p y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl (Conn.refl _ _)
    | tail _ hyz ih =>
      rename_i y z
      rcases adj_insert.1 hyz with hyz | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (h.trans (Conn.of_adj hyz))
        · exact Or.inr (Or.inl ⟨h1, h2.trans (Conn.of_adj hyz)⟩)
        · exact Or.inr (Or.inr ⟨h1, h2.trans (Conn.of_adj hyz)⟩)
      · subst h1 h2
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h, Conn.refl _ _⟩)
        · exact Or.inl (h1.trans h2.symm)
        · exact Or.inl h1
      · subst h1 h2
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨h, Conn.refl _ _⟩)
        · exact Or.inl h1
        · exact Or.inl (h1.trans h2.symm)
  · have hs : F ⊆ insert e F := Finset.subset_insert _ _
    have he : Conn (insert e F) e.p e.q := Conn.of_edge (Finset.mem_insert_self _ _)
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono hs
    · exact ((h1.mono hs).trans he).trans (h2.mono hs)
    · exact ((h1.mono hs).trans he.symm).trans (h2.mono hs)
end ULHC
