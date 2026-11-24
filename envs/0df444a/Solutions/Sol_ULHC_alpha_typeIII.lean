-- Prove2me | solution 1 for ULHC.alpha_typeIII
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:09:29.757305+00:00
-- url     : https://prove2.me/submissions/af3f657b-5262-4054-9114-d08962f5fa37

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_lat1_side_nb
import Theorems.Thm_ULHC_outer1_not_mem
import Theorems.Thm_ULHC_side_back2
import Theorems.Thm_ULHC_side_front2
import Theorems.Thm_ULHC_side_lat2
import Theorems.Thm_ULHC_side_front
import Theorems.Thm_ULHC_side_back_next
import Theorems.Thm_ULHC_back2_not_side_corner
import Theorems.Thm_ULHC_side_lat1_not_mem
import Theorems.Thm_ULHC_Ends_inV
import Theorems.Thm_ULHC_mem_after
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_four_sides_class
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_end_inter
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_even_end_border
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_isCell_of_corners
import Theorems.Thm_ULHC_mem_cells
import Theorems.Thm_ULHC_nOn_zero
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_side_mem_cellE
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
theorem _root_.solution (hα : lat1 (cellJ c s (k + 2)) s ∉ F) :
    nb (cellJ c s (k + 1)) (latA s) ∈ chainCells V (flipCol F c s (k + 2)) (cellJ c s (k + 1)) ∧
      ¬ NotTypeIII V (flipCol F c s (k + 2)) (nb (cellJ c s (k + 1)) (latA s)) := by
  have hcu := hcell (k + 1) le_rfl
  have hck := hcell k (by omega)
  obtain ⟨_, _, f1V, _⟩ := isCell_corners hcu s
  obtain ⟨_, _, k1V, _⟩ := isCell_corners hck s
  have i0 : ∀ e, e ∉ F → ind F e = 0 := fun e h => by simp [ind, h]
  have i1 : ∀ e, e ∈ F → ind F e = 1 := fun e h => by simp [ind, h]
  have uL1 : lat1 (cellJ c s (k + 1)) s ∈ F := (hpat.2.1 (k + 1) (by omega)).1.2 (by omega)
  have uF : front (cellJ c s (k + 1)) s ∉ F := fun h => by
    have := (hpat.2.2 (k + 1) (by omega)).1 h; omega
  have kL1 : lat1 (cellJ c s k) s ∉ F := fun h => by
    have := (hpat.2.1 k (by omega)).1.1 h; omega
  have kF : front (cellJ c s k) s ∉ F := fun h => by
    have := ((hpat.2.2 k (by omega)).1 h).2 (by omega); omega
  -- The outer edges at both lateral corners of `g` are dark (degree count).
  have d1 := deg_front1 (cellJ c s (k + 1)) s F
  rw [hF.2 _ f1V, nb_cellJ, i1 _ uL1, i0 _ uF, i0 _ hα] at d1
  have o1 : outer1 (cellJ c s (k + 1)) s ∈ F := by
    by_contra h; rw [i0 _ h] at d1; omega
  have d0 := deg_front1 (cellJ c s k) s F
  rw [hF.2 _ k1V, nb_cellJ, i0 _ kL1, i0 _ kF, i1 _ uL1] at d0
  have o0 : outer1 (cellJ c s k) s ∈ F := by
    by_contra h; rw [i0 _ h] at d0; omega
  -- The sides and corners of `g`.
  have gF : front (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s (k + 1)) s :=
    side_front _ s
  have gB : back (nb (cellJ c s (k + 1)) (latA s)) s = outer1 (cellJ c s k) s := by
    rw [← nb_cellJ]; exact side_back_next _ s
  have gL2 := side_lat2 (cellJ c s (k + 1)) s
  have gb2 := side_back2 (cellJ c s (k + 1)) s
  have gf2 := side_front2 (cellJ c s (k + 1)) s
  have eB := ends_back (nb (cellJ c s (k + 1)) (latA s)) s
  have eF := ends_front (nb (cellJ c s (k + 1)) (latA s)) s
  have vB := eB.inV (hF.1 _ (gB ▸ o0))
  have vF := eF.inV (hF.1 _ (gF ▸ o1))
  have hg : IsCell V (nb (cellJ c s (k + 1)) (latA s)) :=
    isCell_of_corners _ s vB.1 vB.2 vF.1 vF.2
  -- Its outer side is light: otherwise `g` is a 4-cycle of `F` holding `back2` of the end cell.
  have oF : lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F := by
    intro h
    have hz : Conn F (back1 (nb (cellJ c s (k + 1)) (latA s)) s) (back2 (cellJ c s (k + 1)) s) := by
      refine (eB.conn (gB ▸ o0)).trans ?_
      rw [gb2]; exact end_same hT hk hcell hpat
    exact back2_not_side_corner _ s
      (four_sides_class hF hg s (gB ▸ o0) (gF ▸ o1) h (gL2 ▸ uL1) hz)
  -- After the flip.
  have oF' : lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ flipCol F c s (k + 2) := by
    rw [mem_after, nOn_zero c s (fun m _ => side_lat1_not_mem c s (k + 1) m)]; simp [oF]
  have l2F' : lat2 (nb (cellJ c s (k + 1)) (latA s)) s ∉ flipCol F c s (k + 2) := by
    rw [gL2]; intro h; have := (lat1_after hk hpat (j := k + 1) le_rfl).1 h; omega
  have bF' : back (nb (cellJ c s (k + 1)) (latA s)) s ∈ flipCol F c s (k + 2) := by
    rw [gB, mem_after, nOn_zero c s (fun m _ => outer1_not_mem c s k m)]; simp [o0]
  have fF' : front (nb (cellJ c s (k + 1)) (latA s)) s ∈ flipCol F c s (k + 2) := by
    rw [gF, mem_after, nOn_zero c s (fun m _ => outer1_not_mem c s (k + 1) m)]; simp [o1]
  have hsplit := even_end_border k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  refine ⟨?_, fun h => hsplit ?_⟩
  · obtain ⟨hI, _⟩ := end_inter hF hT hk hcell hpat hsep
    simp only [chainCells, Finset.mem_filter]
    refine ⟨mem_cells.2 hg, Relation.ReflTransGen.single
      ⟨hcu, hg, _, hI, by rw [cellE_frame _ s]; simp, ?_⟩⟩
    rw [lat1_side_nb]; exact side_mem_cellE _ _
  · have h1 := h s bF' fF' oF' l2F'
    have hb := eB.conn bF'
    have hf := eF.conn fF'
    rw [gb2] at hb
    rw [gf2] at hf
    exact (hb.symm.trans h1).trans hf
end ULHC
