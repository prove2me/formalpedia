-- Prove2me | solution 1 for ULHC.runCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:56.277739+00:00
-- url     : https://prove2.me/submissions/3440951c-e983-49f3-8d5b-c15a2e588cf3

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostAlg
import Theorems.Thm_ULHC_roundCost_le
import Theorems.Thm_ULHC_ACell_split
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Good_step
import Theorems.Thm_ULHC_T_ret_bind
import Theorems.Thm_ULHC_T_ret_pure
import Theorems.Thm_ULHC_T_ret_tick
import Theorems.Thm_ULHC_T_time_bind
import Theorems.Thm_ULHC_T_time_pure
import Theorems.Thm_ULHC_T_time_tick
import Theorems.Thm_ULHC_cncompCost_le
import Theorems.Thm_ULHC_step_deg2
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
theorem _root_.solution : ∀ (k : ℕ) (G : Finset Edge), Deg2 V G →
    runCost V k G ≤ (k + 1) * (8000000 * (V.card + 1) ^ 8) := by
  have hN : 1 ≤ V.card + 1 := by omega
  have h4 : (V.card + 1) ^ 3 ≤ (V.card + 1) ^ 8 := Nat.pow_le_pow_right hN (by omega)
  have h5 : 1 ≤ (V.card + 1) ^ 8 := Nat.one_le_pow _ _ hN
  intro k
  induction k with
  | zero =>
    intro G hG
    have := cncompCost_le hG.1
    simp only [runCost]
    omega
  | succ k ih =>
    intro G hG
    have hc := cncompCost_le hG.1
    have hr := roundCost_le hG
    simp only [runCost]
    split
    · nlinarith
    · rcases hs : step V G with _ | G'
      · simp only; nlinarith
      · simp only
        have := ih G' (step_deg2 hG hs)
        nlinarith
end ULHC
