-- Prove2me | solution 1 for ULHC.T.walkT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:35.291371+00:00
-- url     : https://prove2.me/submissions/910d7cde-84f2-4b24-a1d8-8fb01f18d7ba

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TwoFactor
import Theorems.Thm_ULHC_T_fwdT_ret
import Theorems.Thm_ULHC_T_nbrT_ret
import Theorems.Thm_ULHC_T_layerAccT_ret
import Theorems.Thm_ULHC_T_bwdT_ret
import Theorems.Thm_ULHC_T_predT_ret
import Theorems.Thm_ULHC_T_walkT_ret
import Theorems.Thm_ULHC_T_augStepT_ret
import Theorems.Thm_ULHC_T_augLoopT_ret
import Theorems.Thm_ULHC_T_twoFactorT_ret
import Theorems.Thm_ULHC_T_predT_time_le
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_T_cclsT_ret
import Theorems.Thm_ULHC_T_cncompT_ret
import Theorems.Thm_ULHC_T_connBT_ret
import Theorems.Thm_ULHC_T_creachT_ret
import Theorems.Thm_ULHC_T_degT_ret
import Theorems.Thm_ULHC_T_fnbrT_ret
import Theorems.Thm_ULHC_T_isCellT_ret
import Theorems.Thm_ULHC_T_ret_bind
import Theorems.Thm_ULHC_T_ret_pure
import Theorems.Thm_ULHC_T_ret_tick
import Theorems.Thm_ULHC_T_time_bind
import Theorems.Thm_ULHC_T_time_pure
import Theorems.Thm_ULHC_T_time_tick
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v
attribute [local simp] ULHC.T.cclsT_ret
attribute [local simp] ULHC.T.cncompT_ret
attribute [local simp] ULHC.T.connBT_ret
attribute [local simp] ULHC.T.creachT_ret
attribute [local simp] ULHC.T.degT_ret
attribute [local simp] ULHC.T.fnbrT_ret
attribute [local simp] ULHC.T.isCellT_ret
attribute [local simp] ULHC.T.ret_bind
attribute [local simp] ULHC.T.ret_pure
attribute [local simp] ULHC.T.ret_tick
attribute [local simp] ULHC.T.time_bind
attribute [local simp] ULHC.T.time_pure
attribute [local simp] ULHC.T.time_tick


attribute [local simp] ULHC.T.fwdT_ret
attribute [local simp] ULHC.T.nbrT_ret
attribute [local simp] ULHC.T.layerAccT_ret
attribute [local simp] ULHC.T.bwdT_ret
attribute [local simp] ULHC.T.predT_ret
attribute [local simp] ULHC.T.walkT_ret
attribute [local simp] ULHC.T.augStepT_ret
attribute [local simp] ULHC.T.augLoopT_ret
attribute [local simp] ULHC.T.twoFactorT_ret

set_option autoImplicit true
open ULHC ULHC.T
open Finset TF
namespace ULHC.T
theorem _root_.solution (V : Finset Pt) (F0 : Finset Edge) :
    ∀ (Ls : List (Finset Pt)) (v : Pt) (F : Finset Edge), (walkT V F0 Ls v F).time ≤ walkCost V F0 Ls v F
  | [], _, _ => by simp [walkT, walkCost]
  | L :: Ls, v, F => by
    simp only [walkT, walkCost, time_bind, memT, time_tick]
    by_cases hv : v ∈ L
    · simp only [hv, decide_true, ite_true]
      have := solution V F0 Ls v F; omega
    · simp only [hv, decide_false, Bool.false_eq_true, ite_false, time_bind, predT_ret]
      have hp := predT_time_le V F0 L v
      rcases pred V F0 L v with _ | e
      · simp only [time_pure]; omega
      · by_cases hb : Black v
        · simp only [hb, ite_true, time_bind, eraseT, time_tick]
          have := solution V F0 Ls (other e v) (F.erase e); omega
        · simp only [hb, ite_false, time_bind, insertT, time_tick]
          have := solution V F0 Ls (other e v) (insert e F); omega
end ULHC.T
