-- Prove2me | solution 1 for ULHC.flip_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:34.771438+00:00
-- url     : https://prove2.me/submissions/b4d64a18-5650-4cd4-b9b2-82d78b6ede41

import Definitions.Def_ULHC_Graph
import Definitions.Def_ULHC_Flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {c : Pt} (hb : bot c ∈ F) (ht : top c ∈ F) (hl : lft c ∉ F)
    (hr : rgt c ∉ F) :
    flip F c = insert (rgt c) (insert (lft c) ((F.erase (bot c)).erase (top c))) := by
  obtain ⟨x, y⟩ := c
  ext e
  simp only [flip, cellE, Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_erase]
  constructor
  · rintro (⟨he, hn⟩ | ⟨hn, he⟩)
    · push Not at hn; exact Or.inr (Or.inr ⟨hn.2.1, hn.1, he⟩)
    · rcases hn with rfl | rfl | rfl | rfl
      · exact absurd hb he
      · exact absurd ht he
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
  · rintro (rfl | rfl | ⟨h1, h2, he⟩)
    · exact Or.inr ⟨by simp [rgt, bot, top, lft], hr⟩
    · exact Or.inr ⟨by simp [rgt, bot, top, lft], hl⟩
    · refine Or.inl ⟨he, ?_⟩
      rintro (rfl | rfl | rfl | rfl)
      · exact h2 rfl
      · exact h1 rfl
      · exact hl he
      · exact hr he
end ULHC
