-- Prove2me | solution 1 for ULHC.symmDiff_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:17:25.325723+00:00
-- url     : https://prove2.me/submissions/f403b43f-e9f2-4cb1-9ddc-36aa1ec75162

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
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
theorem _root_.solution {F : Finset Edge} {a1 a2 a3 b1 b2 b3 : Edge}
    (ha1 : a1 ∈ F) (ha2 : a2 ∈ F) (ha3 : a3 ∈ F) (hb1 : b1 ∉ F) (hb2 : b2 ∉ F) (hb3 : b3 ∉ F) :
    symmDiff F {b1, a1, a2, a3, b2, b3} =
      (insert b3 (insert b2 (((insert b1 F).erase a1).erase a2))).erase a3 := by
  ext e
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
  constructor
  · rintro (⟨he, hn⟩ | ⟨hn, he⟩)
    · push Not at hn
      exact ⟨hn.2.2.2.1, Or.inr (Or.inr ⟨hn.2.2.1, hn.2.1, Or.inr he⟩)⟩
    · rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨fun h => he (h ▸ ha3), Or.inr (Or.inr ⟨fun h => he (h ▸ ha2),
          fun h => he (h ▸ ha1), Or.inl rfl⟩)⟩
      · exact absurd ha1 he
      · exact absurd ha2 he
      · exact absurd ha3 he
      · exact ⟨fun h => he (h ▸ ha3), Or.inr (Or.inl rfl)⟩
      · exact ⟨fun h => he (h ▸ ha3), Or.inl rfl⟩
  · rintro ⟨h3, rfl | rfl | ⟨h2, h1, rfl | he⟩⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), hb3⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hb2⟩
    · exact Or.inr ⟨Or.inl rfl, hb1⟩
    · refine Or.inl ⟨he, ?_⟩
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact hb1 he
      · exact h1 rfl
      · exact h2 rfl
      · exact h3 rfl
      · exact hb2 he
      · exact hb3 he
end ULHC
