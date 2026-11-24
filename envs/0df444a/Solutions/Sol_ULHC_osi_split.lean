-- Prove2me | solution 1 for ULHC.osi_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:58:20.57414+00:00
-- url     : https://prove2.me/submissions/ce63a967-7456-428f-81bf-1e01e074be64

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_mem_flip_off
import Theorems.Thm_ULHC_split_symm
import Theorems.Thm_ULHC_alt_of_lats
import Theorems.Thm_ULHC_flipCol_flip_comm
import Theorems.Thm_ULHC_stripPat_congr
import Theorems.Thm_P2M_ULHC_alt_corners_conn__04780e54d852
import Theorems.Thm_ULHC_ACell_split
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Deg2_class
import Theorems.Thm_ULHC_Deg2_le_two
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_flip_eq
import Theorems.Thm_ULHC_frame_of_allConn
import Theorems.Thm_ULHC_isCell_corners
import Theorems.Thm_ULHC_mem_flipCol
import Theorems.Thm_ULHC_mkLat_cellE
import Theorems.Thm_ULHC_nOn_zero
import Theorems.Thm_ULHC_planar_lat
import Theorems.Thm_ULHC_strip_even_rel
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hG : Deg2 V G) (hk : k % 2 = 0) (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j))
  (hpat : StripPat G c s (k + 2)) (hsep : ¬ Conn G (back1 c s) (front1 c s))
  (hsame : Conn G (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s))
  (hT' : NoTypeIII V (flipCol G c s (k + 2)))
include hG hk hcell hpat hsep hsame hT'
namespace ULHC
theorem _root_.solution {u : Pt} {tf : Side} (hu : IsCell V u)
    (lu1 : lat1 u tf ∈ G) (lu2 : lat2 u tf ∈ G) (bu : back u tf ∉ G) (fu : front u tf ∉ G)
    (hsu : Conn G (back1 u tf) (back2 u tf))
    (hfar : ∀ j ≤ k + 1, ∀ e ∈ cellE u, e ∉ cellE (cellJ c s j))
    (hmu1 : ¬ IsMid c s k (back1 u tf)) (hmu2 : ¬ IsMid c s k (back2 u tf))
    {x y : Pt} (hxy : Conn G x y) (hsplit : ¬ Conn (flip G u) x y)
    (hx : ¬ IsMid c s k x) (hy : ¬ IsMid c s k y) :
    ¬ Conn (flip (flipCol G c s (k + 2)) u) x y := by
  obtain ⟨F1, hF1, _, _, hrel, _, hodd⟩ := strip_even_rel k hk G hG hcell hpat hsep hsame
  rw [flipCol_flip_comm]
  set H := flip G u
  -- `u`'s flip is a split of `G`: connections of `H` are connections of `G`.
  obtain ⟨ub1, ub2, uf1, uf2⟩ := isCell_corners hu tf
  have hE := mkLat_cellE u tf
  obtain ⟨_, hHG, _⟩ := (mkLat u tf).split hG.1 ub1 uf1 ub2 uf2 lu1 lu2 bu
    (fun z hz => by rcases hz with hz | hz
                    · exact hG.class ub1 hz
                    · exact hG.class ub2 hz) hsu hG.le_two
    (fun K h1 h2 h3 h4 h5 => planar_lat K u tf h1 h2 h3 h4 h5)
  rw [← (mkLat u tf).flip_eq hE lu1 lu2 bu fu] at hHG
  have hH : Deg2 V H := hG.flip (mkLat u tf) hu hE lu1 lu2 bu fu
  -- `a` is still a proper strip of `H`.
  have hcong : ∀ j < k + 2, ∀ e ∈ cellE (cellJ c s j), (e ∈ H ↔ e ∈ G) := by
    intro j hj e he
    exact mem_flip_off (fun h => hfar j (by omega) e h he)
  have hpatH : StripPat H c s (k + 2) := (stripPat_congr hcong).2 hpat
  have hsepH : ¬ Conn H (back1 c s) (front1 c s) := fun h => hsep (hHG _ _ h)
  set ua := cellJ c s (k + 1)
  by_cases hsameH : Conn H (back1 ua s) (back2 ua s)
  · obtain ⟨F2, hF2, _, _, hrel2, _, hodd2⟩ := strip_even_rel k hk H hH hcell hpatH hsepH hsameH
    rw [hodd2 x y hx hy]
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hsplit (hrel2 _ _ h)
    · exact hsep (((hHG _ _ (hrel2 _ _ h1)).symm.trans hxy).trans (hHG _ _ (hrel2 _ _ h2)).symm)
    · exact hsep (((hHG _ _ (hrel2 _ _ h2)).trans hxy.symm).trans (hHG _ _ (hrel2 _ _ h1)))
  · -- `a`'s end cell is split by `u`: then `u` is split by `a`'s end cell, and `u` would be a
    -- Type III cell of `G ⊕ a`.
    exfalso
    have hcua := hcell (k + 1) le_rfl
    obtain ⟨_, hl, hf⟩ := hpat
    have la1 : lat1 ua s ∈ G := (hl (k + 1) (by omega)).1.2 (by omega)
    have la2 : lat2 ua s ∈ G := (hl (k + 1) (by omega)).2.2 (by omega)
    have ba : back ua s ∉ G := by
      rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
    have fa : front ua s ∉ G := by
      intro h; have := (hf (k + 1) (by omega)).1 h; omega
    have hsym := split_symm hG hu hcua lu1 lu2 bu fu la1 la2 ba fa hsu hsame
      (fun e h1 h2 => hfar (k + 1) le_rfl e h1 h2)
    have hn : ¬ Conn (flip G ua) (back1 u tf) (back2 u tf) := fun h => hsameH (hsym.2 h)
    have hn' : ¬ Conn (flipCol G c s (k + 2)) (back1 u tf) (back2 u tf) := by
      rw [hodd _ _ hmu1 hmu2]
      rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hn (hF1 ▸ h)
      · exact hsep (((hrel _ _ h1).symm.trans hsu).trans (hrel _ _ h2).symm)
      · exact hsep (((hrel _ _ h2).trans hsu.symm).trans (hrel _ _ h1))
    -- `u` is alternating in `G ⊕ a` with the same sides.
    have hc' : ∀ e ∈ cellE u, (e ∈ flipCol G c s (k + 2) ↔ e ∈ G) := by
      intro e he
      rw [mem_flipCol, nOn_zero c s (fun j hj => hfar j (by omega) e he)]
      simp
    have mem : ∀ e, e = lat1 u tf ∨ e = lat2 u tf ∨ e = back u tf ∨ e = front u tf → e ∈ cellE u := by
      intro e he; rw [cellE_frame u tf]; rcases he with rfl | rfl | rfl | rfl <;> simp
    have l1' := (hc' _ (mem _ (Or.inl rfl))).2 lu1
    have l2' := (hc' _ (mem _ (Or.inr (Or.inl rfl)))).2 lu2
    have b' : back u tf ∉ flipCol G c s (k + 2) :=
      fun h => bu ((hc' _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))).1 h)
    have f' : front u tf ∉ flipCol G c s (k + 2) :=
      fun h => fu ((hc' _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))).1 h)
    have ha : Alt (flipCol G c s (k + 2)) u := alt_of_lats l1' l2' b' f'
    have hall : AllConn (flipCol G c s (k + 2)) u := by
      unfold AllConn; exact alt_corners_conn' (V := V) (hT' u hu) ha
    exact hn' (frame_of_allConn hall tf).1
end ULHC
