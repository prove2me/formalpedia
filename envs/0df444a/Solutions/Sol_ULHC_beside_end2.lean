-- Prove2me | solution 1 for ULHC.beside_end2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:09:26.76535+00:00
-- url     : https://prove2.me/submissions/6d7137a9-0718-4e8d-9111-b27f51103856

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_side2_back1
import Theorems.Thm_ULHC_side2_front1
import Theorems.Thm_ULHC_side2_lat1
import Theorems.Thm_ULHC_side2_front
import Theorems.Thm_ULHC_side2_back_ends
import Theorems.Thm_ULHC_side2_front_ends
import Theorems.Thm_ULHC_mem_flipCol_out
import Theorems.Thm_ULHC_side2_lat2_not_mem
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_inV
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_end_corners
import Theorems.Thm_ULHC_flipCol_off
import Theorems.Thm_ULHC_isCell_of_corners
import Theorems.Thm_ULHC_lat2_not_mem
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer2_not_mem
import Theorems.Thm_ULHC_outer2_side_nb_next
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hs x0 hconn hF hT hk hcell hpat hsep
omit hs x0 hconn
namespace ULHC
theorem _root_.solution (hb : outer2 (cellJ c s k) s ∈ F) (hf : outer2 (cellJ c s (k + 1)) s ∈ F)
    (hl : lat2 (nb (cellJ c s (k + 1)) (latB s)) s ∉ F) :
    ¬ NoTypeIII V (flipCol F c s (k + 2)) := by
  intro hT'
  set u := cellJ c s (k + 1)
  set L := nb u (latB s)
  have hnbk : nb (cellJ c s k) s = u := nb_cellJ c s k
  have hbL : back L s = outer2 (cellJ c s k) s := by
    rw [outer2_side_nb_next, hnbk]; rfl
  have hfL : front L s = outer2 u s := side2_front u s
  have hout : ∀ e, (e = outer2 (cellJ c s k) s ∨ e = outer2 u s ∨ e = lat2 L s) →
      ∀ j < k + 2, e ∉ cellE (cellJ c s j) := by
    rintro e (rfl | rfl | rfl) j _
    · exact outer2_not_mem c s k j
    · exact outer2_not_mem c s (k + 1) j
    · exact side2_lat2_not_mem c s (k + 1) j
  have hb' : back L s ∈ flipCol F c s (k + 2) := by
    rw [hbL, mem_flipCol_out (hout _ (Or.inl rfl))]; exact hb
  have hf' : front L s ∈ flipCol F c s (k + 2) := by
    rw [hfL, mem_flipCol_out (hout _ (Or.inr (Or.inl rfl)))]; exact hf
  have hl' : lat2 L s ∉ flipCol F c s (k + 2) := by
    rw [mem_flipCol_out (hout _ (Or.inr (Or.inr rfl)))]; exact hl
  have hl1' : lat1 L s ∉ flipCol F c s (k + 2) := by
    rw [side2_lat1, show k + 2 = (k + 1) + 1 from rfl,
      flipCol_off F c s (k + 1) (fun i hi => lat2_not_mem c s (by omega)), mem_flip_iff]
    have : lat2 u s ∈ F := (hpat.2.1 (k + 1) (by omega)).2.2 (by omega)
    intro h; exact (h.1 this) (by rw [cellE_frame u s]; simp [u])
  have hV1 := (side2_back_ends u s).inV (hF.1 _ (hbL ▸ hb))
  have hV2 := (side2_front_ends u s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s ?_ hV1.2 ?_ hV2.2
    · rw [side2_back1]; exact hV1.1
    · rw [side2_front1]; exact hV2.1
  have hLL := hT' L hcL s hb' hf' hl1' hl'
  rw [side2_back1, side2_front1] at hLL
  have hc := end_corners hF hT hk hcell hpat hsep
  exact hc.2.2 ((hc.1.trans hLL).trans hc.2.1.symm)
end ULHC
