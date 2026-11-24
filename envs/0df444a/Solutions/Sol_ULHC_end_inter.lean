-- Prove2me | solution 1 for ULHC.end_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:47:00.461443+00:00
-- url     : https://prove2.me/submissions/7506bf65-f887-41d6-8a80-bcbf751a4817

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_Ends_isEdge
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_GridIso_conn_iff
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_even_end_border
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_mem_GE
import Theorems.Thm_ULHC_mem_cells
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution :
    Inter V (flipCol F c s (k + 2)) (lat1 (cellJ c s (k + 1)) s) ∧
      lat1 (cellJ c s (k + 1)) s ∈
        EB V (flipCol F c s (k + 2)) (cellJ c s (k + 1)) := by
  have hcu := hcell (k + 1) le_rfl
  obtain ⟨b1, _, f1, _⟩ := isCell_corners hcu s
  have hsplit := even_end_border k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  have hE : IsEdge V (lat1 (cellJ c s (k + 1)) s) := (ends_lat1 _ s).isEdge b1 f1
  have hI : Inter V (flipCol F c s (k + 2)) (lat1 (cellJ c s (k + 1)) s) := by
    refine ⟨hE, fun h => ?_, fun h => hsplit (((ends_lat1 _ s).conn_iff _).1 h)⟩
    have := (lat1_after hk hpat (j := k + 1) le_rfl).1 h; omega
  refine ⟨hI, ?_⟩
  simp only [EB, Finset.mem_filter]
  refine ⟨mem_GE.2 hE, hI, cellJ c s (k + 1), ?_, by rw [cellE_frame _ s]; simp⟩
  simp only [chainCells, Finset.mem_filter]
  exact ⟨mem_cells.2 hcu, Relation.ReflTransGen.refl⟩
end ULHC
