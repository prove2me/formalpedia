-- Prove2me | solution 1 for ULHC.decodeCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:29:20.44938+00:00
-- url     : https://prove2.me/submissions/cffcb359-1ff6-47c0-83d0-769926a2be4b

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostAlg
import Theorems.Thm_ULHC_chain_len
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_T_ret_bind
import Theorems.Thm_ULHC_T_ret_pure
import Theorems.Thm_ULHC_T_ret_tick
import Theorems.Thm_ULHC_T_time_bind
import Theorems.Thm_ULHC_T_time_pure
import Theorems.Thm_ULHC_T_time_tick
import Theorems.Thm_ULHC_dval_eq
import Theorems.Thm_ULHC_dval_le
import Theorems.Thm_ULHC_findPath_some
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v
attribute [local simp] ULHC.T.ret_bind
attribute [local simp] ULHC.T.ret_pure
attribute [local simp] ULHC.T.ret_tick
attribute [local simp] ULHC.T.time_bind
attribute [local simp] ULHC.T.time_pure
attribute [local simp] ULHC.T.time_tick



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hGV : Inside V G) : decodeCost V G ≤ Dm V + 2 := by
  unfold decodeCost
  rcases hp : findPath V G with _ | ⟨σ, L⟩
  · simp
  · simp only
    have hP := (findPath_some hGV hp).1
    have h1 := chain_len L σ hP.1.2
    have h2 := dval_le (V := V) hGV
    rw [dval_eq hp] at h2
    unfold wt at h2
    omega
end ULHC
