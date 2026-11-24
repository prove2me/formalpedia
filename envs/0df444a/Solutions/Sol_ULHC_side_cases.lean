-- Prove2me | solution 1 for ULHC.side_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:40.854327+00:00
-- url     : https://prove2.me/submissions/3c8c67a8-9472-4965-a5d4-74b17b91b7e8

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
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
namespace ULHC
theorem _root_.solution (s s' : Side) : s' = s ∨ s' = s.opp ∨ s' = latA s ∨ s' = latB s := by
  cases s <;> cases s' <;> simp [Side.opp, latA, latB]
end ULHC
