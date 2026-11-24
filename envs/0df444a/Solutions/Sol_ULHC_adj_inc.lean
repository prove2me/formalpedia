-- Prove2me | solution 1 for ULHC.adj_inc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:57:03.166248+00:00
-- url     : https://prove2.me/submissions/3fe8b8d7-766b-4da1-9c27-48bc255a9f1a

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_Edge_p_ne_q
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {u v : Pt} (h : Adj F u v) :
    ∃ e ∈ F, (e.p = u ∨ e.q = u) ∧ (e.p = v ∨ e.q = v) ∧ v = other e u := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨e, he, ?_, ?_, ?_⟩
  · rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact Or.inl h1
    · exact Or.inr h2
  · rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact Or.inr h2
    · exact Or.inl h1
  · unfold other
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, h2]
    · have : e.p ≠ u := fun h => Edge.p_ne_q e (h.trans h2.symm)
      rw [if_neg this, h1]
end ULHC
