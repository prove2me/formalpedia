-- Prove2me | solution 1 for ULHC.beyond_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:11:36.591432+00:00
-- url     : https://prove2.me/submissions/f05997f3-8fb8-49af-8212-5991ddcba8f8

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_beside_end1
import Theorems.Thm_ULHC_beside_end2
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_deg_front1
import Theorems.Thm_ULHC_deg_front2
import Theorems.Thm_ULHC_end_side_far1
import Theorems.Thm_ULHC_end_side_far2
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_ind_of_mem
import Theorems.Thm_ULHC_ind_of_not_mem
import Theorems.Thm_ULHC_outer1_body
import Theorems.Thm_ULHC_outer2_body
import Theorems.Thm_ULHC_strip_sig


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
  {z : Pt} {tf : Side} {m : ℕ} (hz : StripPat F z tf m)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hz
omit hs hconn
omit x0
namespace ULHC
theorem _root_.solution (ht : tf = latA s ∨ tf = latB s) (hq : z = nb (cellJ c s (k + 1)) s)
    (hm : 2 ≤ m) : False := by
  set e := cellJ c s (k + 1)
  obtain ⟨_, _, gb, gf⟩ := strip_sig hz (show 0 < m by omega)
  rw [cellJ_zero, hq] at gb gf
  have hfz : front (nb e s) tf ∉ F := fun h => by have := (gf.1 h).2 (by omega); omega
  obtain ⟨a1, a2, _, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have l1 : lat1 e s ∈ F := a1.2 (by omega)
  have l2 : lat2 e s ∈ F := a2.2 (by omega)
  have hfe : front e s ∉ F := fun h => by have := (af.1 h).1 (by omega); omega
  have he := hcell (k + 1) le_rfl
  rcases ht with rfl | rfl
  · rw [(frame_latA (nb e s) s).1] at hfz
    have hd := hF.2 _ (corners4 he s).2.2.1
    rw [deg_front1, ind_of_mem l1, ind_of_not_mem hfe, ind_of_not_mem hfz] at hd
    have ho : outer1 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd; omega
    have hb := (outer1_body hF hcell hpat le_rfl).2 hk
    exact beside_end1 hF hT hk hcell hpat hsep hb ho
      (end_side_far1 hF hT hk hcell hpat hb ho) hT'
  · rw [(frame_latB (nb e s) s).1] at hfz
    have hd := hF.2 _ (corners4 he s).2.2.2
    rw [deg_front2, ind_of_mem l2, ind_of_not_mem hfe, ind_of_not_mem hfz] at hd
    have ho : outer2 e s ∈ F := by by_contra ho; rw [ind_of_not_mem ho] at hd; omega
    have hb := (outer2_body hF hcell hpat le_rfl).2 hk
    exact beside_end2 hF hT hk hcell hpat hsep hb ho
      (end_side_far2 hF hT hk hcell hpat hb ho) hT'
end ULHC
