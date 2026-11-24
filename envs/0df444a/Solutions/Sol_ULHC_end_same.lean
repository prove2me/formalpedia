-- Prove2me | solution 1 for ULHC.end_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:35:21.195419+00:00
-- url     : https://prove2.me/submissions/6b24c38e-c9e3-4ca3-a94d-2f7b80283064

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_frame_of_allConn
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_alt_corners_conn
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_lat1_eq
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
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hT hk hcell hpat
namespace ULHC
theorem _root_.solution : Conn F (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s) := by
  have hu := hcell (k + 1) le_rfl
  obtain ⟨_, hl, hf⟩ := hpat
  have l1 := (hl (k + 1) (by omega)).1.2 (by omega)
  have l2 := (hl (k + 1) (by omega)).2.2 (by omega)
  have fF : front (cellJ c s (k + 1)) s ∉ F := by
    intro h; have := (hf (k + 1) (by omega)).1 h; omega
  have bF : back (cellJ c s (k + 1)) s ∉ F := by
    rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
  -- `u` is alternating with its lateral sides dark: rotate to the frame where they are
  -- back and front.
  have ha : Alt F (cellJ c s (k + 1)) := by
    rw [lat1_eq] at l1; rw [lat2_eq] at l2
    simp only [back, front] at fF bF
    generalize cellJ c s (k + 1) = r at *
    obtain ⟨x, y⟩ := r
    cases s <;> simp only [latA, latB, sideEdge, Side.opp] at l1 l2 fF bF <;> unfold Alt <;> tauto
  exact (frame_of_allConn (alt_corners_conn hT hu ha) s).1
end ULHC
