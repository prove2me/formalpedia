-- Prove2me | solution 1 for ULHC.pot_zero_off_cells
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:29:35.087932+00:00
-- url     : https://prove2.me/submissions/247e6fc4-0248-45aa-b65e-2e2e364d520c

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_pot_around_missing
import Theorems.Thm_ULHC_pot_missing_chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_pot_eq_zero_of_left
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {E : Finset Edge} {w : Edge → ℤ}
  (hS : Supp E w) (hb : Balanced w) (hE : ∀ e ∈ E, e.p ∈ V ∧ e.q ∈ V)
include hS hb hE
namespace ULHC
theorem _root_.solution (hs : Solid V) {c : Pt} (hc : ¬ IsCell V c) : pot E w c = 0 := by
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
  obtain ⟨b, hab, hb'⟩ := hs a ha
  rw [pot_around_missing hS hb hE ha hac, pot_missing_chain hS hb hE hab]
  exact pot_eq_zero_of_left (B := b.1) (fun e he => hb' _ (hE e he).1) b le_rfl
end ULHC
