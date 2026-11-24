-- Prove2me | solution 1 for ULHC.beside_end1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:09:26.257567+00:00
-- url     : https://prove2.me/submissions/ad392e75-164f-42be-b3a3-87014e24905a

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_side_back_ends
import Theorems.Thm_ULHC_side_front_ends
import Theorems.Thm_ULHC_mem_flipCol_out
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_inV
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_end_corners
import Theorems.Thm_ULHC_flipCol_off
import Theorems.Thm_ULHC_isCell_of_corners
import Theorems.Thm_ULHC_lat1_not_mem
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer1_not_mem
import Theorems.Thm_ULHC_side_back2
import Theorems.Thm_ULHC_side_back_next
import Theorems.Thm_ULHC_side_front
import Theorems.Thm_ULHC_side_front2
import Theorems.Thm_ULHC_side_lat1_not_mem
import Theorems.Thm_ULHC_side_lat2
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
theorem _root_.solution (hb : outer1 (cellJ c s k) s ∈ F) (hf : outer1 (cellJ c s (k + 1)) s ∈ F)
    (hl : lat1 (nb (cellJ c s (k + 1)) (latA s)) s ∉ F) :
    ¬ NoTypeIII V (flipCol F c s (k + 2)) := by
  intro hT'
  set u := cellJ c s (k + 1)
  set L := nb u (latA s)
  have hcu : IsCell V u := hcell (k + 1) le_rfl
  have hnbk : nb (cellJ c s k) s = u := nb_cellJ c s k
  have hbL : back L s = outer1 (cellJ c s k) s := by
    rw [← side_back_next, hnbk]
  have hfL : front L s = outer1 u s := side_front u s
  have hout : ∀ e, (e = outer1 (cellJ c s k) s ∨ e = outer1 u s ∨ e = lat1 L s) →
      ∀ j < k + 2, e ∉ cellE (cellJ c s j) := by
    rintro e (rfl | rfl | rfl) j _
    · exact outer1_not_mem c s k j
    · exact outer1_not_mem c s (k + 1) j
    · exact side_lat1_not_mem c s (k + 1) j
  have hb' : back L s ∈ flipCol F c s (k + 2) := by
    rw [hbL, mem_flipCol_out (hout _ (Or.inl rfl))]; exact hb
  have hf' : front L s ∈ flipCol F c s (k + 2) := by
    rw [hfL, mem_flipCol_out (hout _ (Or.inr (Or.inl rfl)))]; exact hf
  have hl' : lat1 L s ∉ flipCol F c s (k + 2) := by
    rw [mem_flipCol_out (hout _ (Or.inr (Or.inr rfl)))]; exact hl
  have hl2' : lat2 L s ∉ flipCol F c s (k + 2) := by
    rw [side_lat2, show k + 2 = (k + 1) + 1 from rfl,
      flipCol_off F c s (k + 1) (fun i hi => lat1_not_mem c s (by omega)), mem_flip_iff]
    have : lat1 u s ∈ F := (hpat.2.1 (k + 1) (by omega)).1.2 (by omega)
    intro h; exact (h.1 this) (by rw [cellE_frame u s]; simp [u])
  have hV1 := (side_back_ends u s).inV (hF.1 _ (hbL ▸ hb))
  have hV2 := (side_front_ends u s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s hV1.1 ?_ hV2.1 ?_
    · rw [side_back2]; exact hV1.2
    · rw [side_front2]; exact hV2.2
  have hLL := hT' L hcL s hb' hf' hl' hl2'
  have hc := end_corners hF hT hk hcell hpat hsep
  apply hc.2.2
  have e1 := side_back_ends u s
  have e2 := side_front_ends u s
  rw [← hfL] at e2
  exact ((e1.conn hb').symm.trans hLL).trans (e2.conn hf')
end ULHC
