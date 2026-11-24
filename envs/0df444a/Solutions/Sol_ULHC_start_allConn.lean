-- Prove2me | solution 1 for ULHC.start_allConn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:55:24.958774+00:00
-- url     : https://prove2.me/submissions/6ad7f13c-6997-48b1-9f18-060515b10f96

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Created
import Theorems.Thm_P2M_ULHC_alt_corners_conn__04780e54d852
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_after
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_front_after
import Theorems.Thm_ULHC_lat1_after
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_after
import Theorems.Thm_ULHC_lat2_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
include hs x0 hconn hF hT hk hcell hpat hsep hT'
omit hs x0 hconn hF hT
namespace ULHC
theorem _root_.solution : AllConn (flipCol F c s (k + 2)) c := by
  have l1 := (lat1_after hk hpat (j := 0) (by omega)).2 rfl
  have l2 := (lat2_after hk hpat (j := 0) (by omega)).2 rfl
  have fr : front c s ∉ flipCol F c s (k + 2) := by
    have := (front_after hk hpat (j := 0) (by omega)); rw [cellJ_zero] at this
    intro h; have := this.1 h; omega
  have bk := back_after hk hpat
  rw [cellJ_zero] at l1 l2
  have hc : IsCell V c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  have ha : Alt (flipCol F c s (k + 2)) c := by
    rw [lat1_eq] at l1; rw [lat2_eq] at l2
    simp only [back, front] at fr bk
    obtain ⟨x, y⟩ := c
    cases s <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 fr bk <;> unfold Alt <;> tauto
  unfold AllConn
  exact alt_corners_conn' (V := V) (hT' c hc) ha
end ULHC
