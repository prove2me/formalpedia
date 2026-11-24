-- Prove2me | solution 1 for ULHC.T.layerAccT_ret
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:30:33.570865+00:00
-- url     : https://prove2.me/submissions/b5cab85e-d665-482b-bd42-2d52671771f5

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TwoFactor
import Theorems.Thm_ULHC_T_fwdT_ret
import Theorems.Thm_ULHC_T_nbrT_ret
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_TF_layerAcc_eq
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

set_option autoImplicit true
open ULHC ULHC.T
open Finset TF
namespace ULHC.T
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) :
    ∀ k, (layerAccT V F k).ret = layerAcc V F k
  | 0 => by
    simp only [layerAccT, layerAcc, ret_bind, ret_pure, filterT, degT_ret]
    congr 2
    ext z
    simp
  | k + 1 => by
    have ih := solution V F k
    simp only [layerAccT, layerAcc, ret_bind, ih]
    rw [layerAcc_eq]
    simp [unionT, biUnionT]
end ULHC.T
