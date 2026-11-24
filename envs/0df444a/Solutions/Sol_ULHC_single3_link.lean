-- Prove2me | solution 1 for ULHC.single3_link
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:19:07.015627+00:00
-- url     : https://prove2.me/submissions/8093943b-2556-464c-973c-984bba22f1a0

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_endCell_mk2
import Theorems.Thm_ULHC_along_not_mem
import Theorems.Thm_ULHC_along_not_mid
import Theorems.Thm_ULHC_front1_not_corner
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_APair_flip
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
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_alt_corners_conn
import Theorems.Thm_ULHC_alt_frame
import Theorems.Thm_ULHC_alt_of_lats
import Theorems.Thm_ULHC_back_nb
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_inj
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_four_sides_class
import Theorems.Thm_ULHC_frame_ne
import Theorems.Thm_ULHC_frame_of_allConn
import Theorems.Thm_ULHC_mem_flip_off
import Theorems.Thm_ULHC_mkLat_cellE
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_shared_unique
import Theorems.Thm_ULHC_single_pat
import Theorems.Thm_ULHC_strip_sig
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
    (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
    (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat G c s (k + 2))
    (hd1 : lat1 (cellJ c s (k + 2)) s ∈ G) (hd2 : lat2 (cellJ c s (k + 2)) s ∈ G)
    (hdf : front (cellJ c s (k + 2)) s ∈ G) (hcu : IsCell V (cellJ c s (k + 3)))
    {tu : Side} (lu1 : lat1 (cellJ c s (k + 3)) tu ∈ G) (lu2 : lat2 (cellJ c s (k + 3)) tu ∈ G)
    (bu : back (cellJ c s (k + 3)) tu ∉ G) (fu : front (cellJ c s (k + 3)) tu ∉ G)
    (hcd : IsCell V (cellJ c s (k + 2))) :
    CR2 V G ⟨c, s, k + 2⟩ ⟨cellJ c s (k + 3), s, 1⟩ := by
  set e := cellJ c s (k + 1)
  set d := cellJ c s (k + 2)
  set u := cellJ c s (k + 3)
  have hde : nb e s = d := nb_cellJ c s (k + 1)
  have hdu : nb d s = u := nb_cellJ c s (k + 2)
  have afu := alt_frame s lu1 lu2 bu fu
  have hbu : back u s ∈ G := by rw [← hdu, back_nb]; exact hdf
  have hfu : front u s ∈ G := afu.1.1 hbu
  have hl1u : lat1 u s ∉ G := fun h => (afu.2.2.1 hbu) h
  have hl2u : lat2 u s ∉ G := fun h => hl1u (afu.2.1.2 h)
  have hoffe : ∀ x ∈ cellE u, x ∉ cellE e := fun x hx => along_not_mem c s (by omega) hx
  have hflipu : ∀ x ∈ cellE u, (x ∈ flip G e ↔ x ∈ G) := fun x hx => mem_flip_off (hoffe x hx)
  have memu : ∀ y, y = lat1 u s ∨ y = lat2 u s ∨ y = back u s ∨ y = front u s → y ∈ cellE u := by
    intro y hy; rw [cellE_frame _ s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨a1, a2, ab, af⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
  have el1 : lat1 e s ∈ G := a1.2 (by omega)
  have el2 : lat2 e s ∈ G := a2.2 (by omega)
  have eb : back e s ∉ G := fun h => by have := ab.1 h; omega
  have ef : front e s ∉ G := fun h => by have := (af.1 h).1 (by omega); omega
  have hce := hcell (k + 1) le_rfl
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, le_rfl, ?_, fun j hj => ?_, fun j hj i hi x hx => ?_,
    fun j hj => ?_, fun h => by simp at h, ?_, ?_, ?_, ?_⟩
  · rw [endCell_mk2]
    exact single_pat ((hflipu _ (memu _ (Or.inr (Or.inr (Or.inl rfl))))).2 hbu)
      (fun h => hl1u ((hflipu _ (memu _ (Or.inl rfl))).1 h))
      (fun h => hl2u ((hflipu _ (memu _ (Or.inr (Or.inl rfl)))).1 h))
      ((hflipu _ (memu _ (Or.inr (Or.inr (Or.inr rfl))))).2 hfu)
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; exact hcu
  · simp only at hj hi
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero] at hx
    exact along_not_mem c s (by omega) hx
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero, endCell_mk2]
    intro h; have := cellJ_inj c s h; omega
  · rw [show k + 2 - 2 = k from rfl]; exact (along_not_mid c s k).1
  · rw [show k + 2 - 2 = k from rfl]; exact (along_not_mid c s k).2
  · exact (frame_of_allConn (alt_corners_conn hT hcu (alt_of_lats lu1 lu2 bu fu)) s).2.1
  · rw [endCell_mk2]
    intro h
    -- In `flip G e`, the cell `d` has four dark sides.
    --
    have hGe : Deg2 V (flip G e) := hG.flip (mkLat e s) hce (mkLat_cellE e s) el1 el2 eb ef
    have hoffd : ∀ x ∈ cellE d, x ≠ back d s → x ∉ cellE e := by
      intro x hx hxb hxe
      apply hxb
      rw [shared_unique hde.symm hxe hx, ← hde, back_nb]; rfl
    have memd : ∀ y, y = lat1 d s ∨ y = lat2 d s ∨ y = back d s ∨ y = front d s → y ∈ cellE d := by
      intro y hy; rw [cellE_frame _ s]; rcases hy with rfl | rfl | rfl | rfl <;> simp
    have fne := frame_ne d s
    have f1 : lat1 d s ∈ flip G e :=
      (mem_flip_off (hoffd _ (memd _ (Or.inl rfl)) fne.1.symm)).2 hd1
    have f2 : lat2 d s ∈ flip G e :=
      (mem_flip_off (hoffd _ (memd _ (Or.inr (Or.inl rfl))) fne.2.1.symm)).2 hd2
    have f4 : front d s ∈ flip G e :=
      (mem_flip_off (hoffd _ (memd _ (Or.inr (Or.inr (Or.inr rfl)))) fne.2.2.2.2.2.symm)).2 hdf
    have f3 : back d s ∈ flip G e := by
      rw [mem_flip_iff]
      have hfe : back d s = front e s := by rw [← hde, back_nb]
      have hm : front e s ∈ cellE e := by rw [cellE_frame e s]; simp
      rw [hfe]; tauto
    have hb1 : back1 u s = front1 d s := by
      rw [← hdu]; obtain ⟨p, q⟩ := d; cases s <;> simp [back1, front1, nb]
    rw [hb1] at h
    have h' := (ends_lat1 d s).conn f1 |>.trans h
    have := four_sides_class hGe hcd s f3 f4 f1 f2 h'
    rw [← hdu] at this
    exact front1_not_corner d s this
end ULHC
