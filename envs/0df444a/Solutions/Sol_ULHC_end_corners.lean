-- Prove2me | solution 1 for ULHC.end_corners
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:46:43.933529+00:00
-- url     : https://prove2.me/submissions/db689fab-39f5-4af0-8b43-e72fc4bc1cc9

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Created
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_back2_nb
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_end_not_mid
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_even_end_border
import Theorems.Thm_ULHC_front_corner_ne
import Theorems.Thm_ULHC_front_end_after
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_strip_even_rel
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
omit hs x0 hconn hT'
namespace ULHC
theorem _root_.solution :
    Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s) (back2 (cellJ c s (k + 1)) s) ∧
      Conn (flipCol F c s (k + 2)) (front1 (cellJ c s (k + 1)) s)
        (front2 (cellJ c s (k + 1)) s) ∧
      ¬ Conn (flipCol F c s (k + 2)) (back1 (cellJ c s (k + 1)) s)
        (front1 (cellJ c s (k + 1)) s) := by
  have hsame := end_same hT hk hcell hpat
  refine ⟨?_, (ends_front _ s).conn (front_end_after hk hpat),
    even_end_border k hk F hF hcell hpat hsep hsame⟩
  obtain ⟨F1, hF1, _, _, _, _, hodd⟩ := strip_even_rel k hk F hF hcell hpat hsep hsame
  -- `back u` is in `F1` (the end cell's own flip), and the back corners are not middles.
  have hb : back (cellJ c s (k + 1)) s ∈ F1 := by
    rw [hF1, mem_flip_iff]
    have uB : back (cellJ c s (k + 1)) s ∉ F := by
      rw [back_cellJ_succ]; intro h; have := (hpat.2.2 k (by omega)).1 h; omega
    have : back (cellJ c s (k + 1)) s ∈ cellE (cellJ c s (k + 1)) := by
      rw [cellE_frame _ s]; simp
    tauto
  have n1 := (end_not_mid c s k).1
  have n2 : ¬ IsMid c s k (back2 (cellJ c s (k + 1)) s) := by
    rw [← nb_cellJ, back2_nb]
    rintro ⟨j, _, hj, h | h⟩
    · exact (front_corner_ne c s (i := k) (j := j) (by omega)).2.2.1 h
    · exact (front_corner_ne c s (i := k) (j := j) (by omega)).2.2.2 h
  exact (hodd _ _ n1 n2).2 (Or.inl ((ends_back _ s).conn hb))
end ULHC
