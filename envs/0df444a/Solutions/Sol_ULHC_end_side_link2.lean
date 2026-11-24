-- Prove2me | solution 1 for ULHC.end_side_link2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:13:19.878023+00:00
-- url     : https://prove2.me/submissions/ddd54619-bbc2-4d86-a8ec-18df6ef6724e

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Theorems.Thm_ULHC_single_pat
import Theorems.Thm_ULHC_nbB_ne
import Theorems.Thm_ULHC_endCell_mk
import Theorems.Thm_ULHC_end_flip_sep
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
import Theorems.Thm_ULHC_Ends_inV
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_end_side_far2
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_isCell_of_corners
import Theorems.Thm_ULHC_lat2_not_mem
import Theorems.Thm_ULHC_mem_flip_off
import Theorems.Thm_ULHC_mid_touch
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_outer2_body
import Theorems.Thm_ULHC_outer2_not_mem
import Theorems.Thm_ULHC_outer2_side_nb_next
import Theorems.Thm_ULHC_side2_back1
import Theorems.Thm_ULHC_side2_back_ends
import Theorems.Thm_ULHC_side2_front
import Theorems.Thm_ULHC_side2_front1
import Theorems.Thm_ULHC_side2_front_ends
import Theorems.Thm_ULHC_side2_lat1
import Theorems.Thm_ULHC_side2_lat2_not_mem
import Theorems.Thm_ULHC_strip_sig
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution (hf : outer2 (cellJ c s (k + 1)) s ∈ F) :
    CR2 V F ⟨c, s, k + 2⟩ ⟨nb (cellJ c s (k + 1)) (latB s), s, 1⟩ := by
  set e := cellJ c s (k + 1)
  set L := nb e (latB s)
  have hb0 := (outer2_body hF hcell hpat le_rfl).2 hk
  have hbL : back L s = outer2 (cellJ c s k) s := by rw [outer2_side_nb_next, nb_cellJ]; rfl
  have hfL : front L s = outer2 e s := side2_front e s
  have hfar := end_side_far2 hF hT hk hcell hpat hb0 hf
  have hl2e : lat2 e s ∈ F := (strip_sig hpat (show k + 1 < k + 2 by omega)).2.1.2 (by omega)
  have offL : ∀ i ≤ k + 1, back L s ∉ cellE (cellJ c s i) ∧ front L s ∉ cellE (cellJ c s i) ∧
      lat2 L s ∉ cellE (cellJ c s i) := fun i _ =>
    ⟨by rw [hbL]; exact outer2_not_mem c s k i, by rw [hfL]; exact outer2_not_mem c s (k + 1) i,
      side2_lat2_not_mem c s (k + 1) i⟩
  have hV1 := (side2_back_ends e s).inV (hF.1 _ (hbL ▸ hb0))
  have hV2 := (side2_front_ends e s).inV (hF.1 _ hf)
  have hcL : IsCell V L := by
    refine isCell_of_corners L s ?_ hV1.2 ?_ hV2.2
    · rw [side2_back1]; exact hV1.1
    · rw [side2_front1]; exact hV2.1
  have hmemL : ∀ y ∈ cellE L, y = back L s ∨ y = front L s ∨ y = lat1 L s ∨ y = lat2 L s := by
    intro y hy; rw [cellE_frame L s] at hy; simpa using hy
  have hmid : ∀ p (x : Edge), x ∈ F → (x.p = p ∨ x.q = p) →
      (∀ i ≤ k + 1, x ∉ cellE (cellJ c s i)) → ¬ IsMid c s k p := fun p x hx hxp hoff hm => by
    obtain ⟨i, hi, hxi⟩ := mid_touch hF hpat hcell hm hx hxp
    exact hoff i (by omega) hxi
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [endCell_mk]
    refine single_pat ?_ ?_ ?_ ?_
    · rw [mem_flip_off (offL (k + 1) le_rfl).1]; rw [hbL]; exact hb0
    · rw [side2_lat1, mem_flip_iff]
      intro h; exact (h.1 hl2e) (by rw [cellE_frame e s]; simp)
    · rw [mem_flip_off (offL (k + 1) le_rfl).2.2]; exact hfar
    · rw [mem_flip_off (offL (k + 1) le_rfl).2.1, hfL]; exact hf
  · intro j hj; obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; exact hcL
  · intro j hj i hi y hy
    simp only at hj hi
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero] at hy
    rcases hmemL y hy with rfl | rfl | rfl | rfl
    · exact (offL i (by omega)).1
    · exact (offL i (by omega)).2.1
    · rw [side2_lat1]; exact lat2_not_mem c s (by omega)
    · exact (offL i (by omega)).2.2
  · intro j hj; obtain rfl : j = 0 := by omega
    rw [cellJ_zero, endCell_mk]; exact nbB_ne e s
  · intro h; simp at h
  · show ¬ IsMid c s (k + 2 - 2) _
    rw [show k + 2 - 2 = k by omega]
    exact hmid _ _ (hbL ▸ hb0) ((ends_back L s).inc_iff _ |>.2 (Or.inl rfl))
      (fun i hi => (offL i hi).1)
  · show ¬ IsMid c s (k + 2 - 2) _
    rw [show k + 2 - 2 = k by omega]
    exact hmid _ _ (hfL ▸ hf) ((ends_front L s).inc_iff _ |>.2 (Or.inl rfl))
      (fun i hi => (offL i hi).2.1)
  · rw [side2_back1, side2_front1]; exact (ends_lat2 e s).conn hl2e
  · rw [endCell_mk, side2_back1, side2_front1]
    intro h
    have hbe : back e s ∈ flip F e := by
      rw [mem_flip_iff]
      have : back e s ∉ F := fun h' => by
        have := (strip_sig hpat (show k + 1 < k + 2 by omega)).2.2.1.1 h'; omega
      exact ⟨fun h' => absurd h' this, fun hn => absurd (by rw [cellE_frame e s]; simp) hn⟩
    have hfe : front e s ∈ flip F e := by
      rw [mem_flip_iff]
      have : front e s ∉ F := fun h' => by
        have := ((strip_sig hpat (show k + 1 < k + 2 by omega)).2.2.2.1 h').1 (by omega); omega
      exact ⟨fun h' => absurd h' this, fun hn => absurd (by rw [cellE_frame e s]; simp) hn⟩
    exact end_flip_sep hF hT hk hcell hpat hsep
      ((((ends_back e s).conn hbe).trans h).trans ((ends_front e s).conn hfe).symm)
end ULHC
