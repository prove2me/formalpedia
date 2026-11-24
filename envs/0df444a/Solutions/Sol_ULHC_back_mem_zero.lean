-- Prove2me | solution 1 for ULHC.back_mem_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:40:51.255806+00:00
-- url     : https://prove2.me/submissions/3b0b4c20-9f7d-4f97-b5b3-161e79de4a5e

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
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
theorem _root_.solution : back c s ∈ cellE (cellJ c s 0) := by
  rw [cellJ_zero, cellE_frame c s]; simp
end ULHC
