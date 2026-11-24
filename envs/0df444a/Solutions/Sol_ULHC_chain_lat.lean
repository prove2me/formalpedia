-- Prove2me | solution 1 for ULHC.chain_lat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:39:14.58629+00:00
-- url     : https://prove2.me/submissions/2e9209f5-28ec-4be5-a883-8380971893a7

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_cell_of_side
import Theorems.Thm_ULHC_nb_cellJ
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution {b c : StripSpec} (hl : CR2 V G b c) (hok : ChainOK b c)
    (hlu : lat1 (endCell b) b.s ∈ G ∧ lat2 (endCell b) b.s ∈ G) {x : Edge}
    (hx : x ∈ cellE c.c) (hxu : x ∈ cellE (endCell b)) :
    x = lat1 c.c c.s ∨ x = lat2 c.c c.s := by
  have hx0 : x ∈ cellE (cellJ c.c c.s 0) := by rw [cellJ_zero]; exact hx
  obtain ⟨_, hxl⟩ := hok 0 hl.2.2.1 x hx0 hxu
  have hxG : x ∈ G := by rcases hxl with rfl | rfl; exacts [hlu.1, hlu.2]
  have hxF : x ∉ flip G (endCell b) := by
    rw [mem_flip_iff]; intro h; exact (h.1 hxG) hxu
  obtain ⟨hb, hlt, hf⟩ := hl.2.2.2.1
  rw [cellE_frame c.c c.s] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact absurd hb hxF
  · exfalso
    have hf0 := hf 0 hl.2.2.1
    rw [cellJ_zero] at hf0
    by_cases h1 : 1 < c.n
    · -- The next cell would be `b`'s end cell.
      --
      have hc1 : cellJ c.c c.s 1 = endCell b := by
        rcases cell_of_side c.c (tf := c.s) hxu with h | h
        · exfalso
          have := hl.2.2.2.2.2.2.1 0 hl.2.2.1
          rw [cellJ_zero] at this; exact this h.symm
        · rw [h]
          have := nb_cellJ c.c c.s 0
          rw [cellJ_zero] at this; exact this.symm
      exact hl.2.2.2.2.2.2.1 1 h1 hc1
    · exact hxF (hf0.2 ⟨fun h => by omega, fun h => by omega⟩)
  · exact Or.inl rfl
  · exact Or.inr rfl
end ULHC
