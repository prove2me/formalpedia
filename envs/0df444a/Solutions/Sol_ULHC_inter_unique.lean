-- Prove2me | solution 1 for ULHC.inter_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:38:53.833353+00:00
-- url     : https://prove2.me/submissions/3aaf451d-d391-4b3b-84af-55ececa4a2d3

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
import Theorems.Thm_ULHC_shared_unique
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
import Theorems.Thm_ULHC_cell_of_side
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {d u : Pt} (hne : d ≠ u) {x y : Edge} (hx : x ∈ cellE d) (hxu : x ∈ cellE u)
    (hy : y ∈ cellE d) (hyu : y ∈ cellE u) : x = y := by
  have hnb : ∃ t', u = nb d t' := by
    rw [cellE_frame d .t] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hside : ∀ t', x = sideEdge d t' → ∃ t'', u = nb d t'' := fun t' h =>
      ⟨t', (cell_of_side d (tf := t') (h ▸ hxu)).resolve_left (Ne.symm hne)⟩
    rcases hx with rfl | rfl | rfl | rfl
    · exact hside _ rfl
    · exact hside _ rfl
    · exact hside _ (lat1_eq _ _)
    · exact hside _ (lat2_eq _ _)
  obtain ⟨t', ht'⟩ := hnb
  rw [shared_unique ht' hx hxu, shared_unique ht' hy hyu]
end ULHC
