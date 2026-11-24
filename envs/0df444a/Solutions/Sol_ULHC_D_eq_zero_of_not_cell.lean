-- Prove2me | solution 1 for ULHC.D_eq_zero_of_not_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:26.575214+00:00
-- url     : https://prove2.me/submissions/3de7f6c4-7145-472a-8e72-6448af0f8638

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_D_around
import Theorems.Thm_ULHC_D_chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_pot_eq_zero_of_left
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
variable (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH
namespace ULHC
theorem _root_.solution (hs : Solid V) {c : Pt} (hc : ¬ IsCell V c) :
    D F H c = 0 := by
  obtain ⟨x, y⟩ := c
  have corner : ∃ a, a ∉ V ∧ Around a (x, y) := by
    unfold IsCell at hc
    by_cases h1 : (x, y) ∈ V
    · by_cases h2 : (x + 1, y) ∈ V
      · by_cases h3 : (x, y + 1) ∈ V
        · refine ⟨(x + 1, y + 1), fun h4 => hc ⟨h1, h2, h3, h4⟩, ?_⟩
          simp [Around]
        · exact ⟨(x, y + 1), h3, by simp [Around]⟩
      · exact ⟨(x + 1, y), h2, by simp [Around]⟩
    · exact ⟨(x, y), h1, by simp [Around]⟩
  obtain ⟨a, ha, hac⟩ := corner
  obtain ⟨b, hab, hb⟩ := hs a ha
  rw [D_around hF hH ha hac, D_chain hF hH hab]
  apply pot_eq_zero_of_left (B := b.1) _ b le_rfl
  intro e he
  rw [Finset.mem_symmDiff] at he
  rcases he with ⟨he, _⟩ | ⟨he, _⟩
  · exact hb _ (hF.1 e he).1
  · exact hb _ (hH.1 e he).1
end ULHC
