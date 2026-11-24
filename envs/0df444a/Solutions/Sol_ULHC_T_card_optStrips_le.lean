-- Prove2me | solution 1 for ULHC.T.card_optStrips_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:57.210952+00:00
-- url     : https://prove2.me/submissions/1418a8de-d87d-459a-a1fc-791f1728d5d0

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
import Theorems.Thm_ULHC_T_ret_pure
import Theorems.Thm_ULHC_T_time_pure
import Theorems.Thm_ULHC_T_ret_bind
import Theorems.Thm_ULHC_T_time_bind
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


attribute [local simp] ULHC.T.ret_pure
attribute [local simp] ULHC.T.time_pure
attribute [local simp] ULHC.T.ret_bind
attribute [local simp] ULHC.T.time_bind

set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}
namespace ULHC.T
theorem _root_.solution (c : Pt) (s : Side) (o : Option ℕ) : (optStrips c s o).card ≤ 1 := by
  unfold optStrips; cases o <;> simp
end ULHC.T
