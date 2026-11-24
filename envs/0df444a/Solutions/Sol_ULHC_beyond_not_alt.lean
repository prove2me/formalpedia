-- Prove2me | solution 1 for ULHC.beyond_not_alt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:48:11.542798+00:00
-- url     : https://prove2.me/submissions/c7262610-944a-48ac-bd10-0e7698ce6c2c

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_mem_after
import Theorems.Thm_ULHC_front_end_after
import Theorems.Thm_ULHC_alt_adj
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat1_not_mem
import Theorems.Thm_ULHC_latA_opp
import Theorems.Thm_ULHC_nOn_zero
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
include hk hpat
namespace ULHC
theorem _root_.solution (h1 : lat1 (cellJ c s (k + 2)) s ∈ F) :
    ¬ Alt (flipCol F c s (k + 2)) (cellJ c s (k + 2)) := by
  intro ha
  have hb : back (cellJ c s (k + 2)) s ∈ flipCol F c s (k + 2) := by
    rw [back_cellJ_succ]; exact front_end_after hk hpat
  have hl : lat1 (cellJ c s (k + 2)) s ∈ flipCol F c s (k + 2) := by
    rw [mem_after, nOn_zero c s (fun m hm => lat1_not_mem c s (by omega))]; simp [h1]
  have := (alt_adj ha s.opp).1
  rw [latA_opp, ← lat1_eq] at this
  exact (this.1 hb) hl
end ULHC
