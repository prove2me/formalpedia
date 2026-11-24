-- Prove2me | solution 1 for ULHC.nb_comm_lat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:51.501518+00:00
-- url     : https://prove2.me/submissions/08622a47-f190-45b0-9df1-2eab51078071

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)
namespace ULHC
theorem _root_.solution (j : ℕ) :
    nb (nb (cellJ c s j) (latA s)) s = nb (cellJ c s (j + 1)) (latA s) ∧
      nb (nb (cellJ c s j) (latB s)) s = nb (cellJ c s (j + 1)) (latB s) := by
  obtain ⟨a, b⟩ := c
  cases s <;> simp [nb, cellJ, latA, latB] <;> ring
end ULHC
