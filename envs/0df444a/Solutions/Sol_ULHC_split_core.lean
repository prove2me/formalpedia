-- Prove2me | solution 1 for ULHC.split_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:25:07.681778+00:00
-- url     : https://prove2.me/submissions/3dc7d881-647a-47e3-ab2b-1706eb761d74

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_alt_touch
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_mid_touch
import Theorems.Thm_ULHC_split_end_t3
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
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
  {z : Pt} {tf : Side} {m : ℕ} (hz : StripPat F z tf m)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hz
omit hs hconn hz
omit x0
namespace ULHC
theorem _root_.solution {w : Pt} {tw : Side} (hw : IsCell V w) (l1 : lat1 w tw ∈ F)
    (l2 : lat2 w tw ∈ F) (bw : back w tw ∉ F) (fw : front w tw ∉ F)
    (hwe : w ≠ cellJ c s (k + 1)) (hwu : w ≠ nb (cellJ c s (k + 1)) s)
    (hsplit : ¬ Conn (flip F w) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s)) :
    False := by
  have hdisj : ∀ j < k + 2, ∀ x ∈ cellE w, x ∉ cellE (cellJ c s j) := by
    intro j hj x hx1 hx2
    rcases alt_touch hF hT hk hcell hpat hsep l1 l2 bw fw hj hx1 hx2 with h | h
    · exact hwe h
    · exact hwu h
  have hmid : ∀ y, y = lat1 w tw ∨ y = lat2 w tw → y ∈ cellE w := by
    intro y hy; rw [cellE_frame w tw]; rcases hy with rfl | rfl <;> simp
  have hm1 : ¬ IsMid c s k (back1 w tw) := fun hm => by
    obtain ⟨j, hj, hx⟩ := mid_touch hF hpat hcell hm l1 ((ends_lat1 w tw).inc_iff _ |>.2 (Or.inl rfl))
    exact hdisj j hj _ (hmid _ (Or.inl rfl)) hx
  have hm2 : ¬ IsMid c s k (back2 w tw) := fun hm => by
    obtain ⟨j, hj, hx⟩ := mid_touch hF hpat hcell hm l2 ((ends_lat2 w tw).inc_iff _ |>.2 (Or.inl rfl))
    exact hdisj j hj _ (hmid _ (Or.inr rfl)) hx
  exact split_end_t3 hF hT hk hcell hpat hsep hw l1 l2 bw fw hdisj hm1 hm2 hsplit hT'
end ULHC
