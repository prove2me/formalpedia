-- Prove2me | solution 1 for ULHC.split_end_t3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:02:56.052936+00:00
-- url     : https://prove2.me/submissions/1f8f707c-e4c5-4401-8f49-88dc1d24aaef

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_mem_flipCol_out
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
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_alt_corners_conn
import Theorems.Thm_ULHC_alt_of_lats
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_frame_of_allConn
import Theorems.Thm_ULHC_split_symm
import Theorems.Thm_ULHC_strip_even_rel
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
theorem _root_.solution {w : Pt} {tw : Side} (hw : IsCell V w)
    (l1 : lat1 w tw ∈ F) (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F)
    (hdisj : ∀ j < k + 2, ∀ x ∈ cellE w, x ∉ cellE (cellJ c s j))
    (hm1 : ¬ IsMid c s k (back1 w tw)) (hm2 : ¬ IsMid c s k (back2 w tw))
    (hsplit : ¬ Conn (flip F w) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    ¬ NoTypeIII V (flipCol F c s (k + 2)) := by
  intro hT'
  set u := cellJ c s (k + 1)
  have hu : IsCell V u := hcell (k + 1) le_rfl
  have hse := end_same hT hk hcell hpat
  have hsw : Conn F (back1 w tw) (back2 w tw) :=
    (frame_of_allConn (alt_corners_conn hT hw (alt_of_lats l1 l2 bw fw)) tw).1
  have hl := hpat.2.1
  have hf := hpat.2.2
  have uL1 : lat1 u s ∈ F := (hl (k + 1) (by omega)).1.2 (by omega)
  have uL2 : lat2 u s ∈ F := (hl (k + 1) (by omega)).2.2 (by omega)
  have uB : back u s ∉ F := by
    rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
  have uF : front u s ∉ F := by
    intro h; have := (hf (k + 1) (by omega)).1 h; omega
  have hdu : ∀ x, x ∈ cellE w → x ∉ cellE u := fun x hx => hdisj (k + 1) (by omega) x hx
  have hsym := split_symm hF hw hu l1 l2 bw fw uL1 uL2 uB uF hsw hse hdu
  have hne : ¬ Conn (flip F u) (back1 w tw) (back2 w tw) := fun h => hsplit (hsym.2 h)
  obtain ⟨F1, hF1, _, _, hsub, _, hodd⟩ := strip_even_rel k hk F hF hcell hpat hsep hse
  have hkeep : ∀ x ∈ cellE w, (x ∈ flipCol F c s (k + 2) ↔ x ∈ F) := fun x hx =>
    mem_flipCol_out (fun j hj => hdisj j hj x hx)
  have sw : ∀ x, x = lat1 w tw ∨ x = lat2 w tw ∨ x = back w tw ∨ x = front w tw → x ∈ cellE w := by
    intro x hx; rw [cellE_frame w tw]; rcases hx with rfl | rfl | rfl | rfl <;> simp
  have ha' : Alt (flipCol F c s (k + 2)) w := alt_of_lats
    ((hkeep _ (sw _ (Or.inl rfl))).2 l1) ((hkeep _ (sw _ (Or.inr (Or.inl rfl)))).2 l2)
    (fun h => bw ((hkeep _ (sw _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
    (fun h => fw ((hkeep _ (sw _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
  have hc := (frame_of_allConn (alt_corners_conn hT' hw ha') tw).1
  rw [hodd _ _ hm1 hm2] at hc
  rcases hc with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hF1] at h; exact hne h
  · exact hsep (((hsub _ _ h1).symm.trans hsw).trans (hsub _ _ h2).symm)
  · exact hsep (((hsub _ _ h2).trans hsw.symm).trans (hsub _ _ h1))
end ULHC
