-- Prove2me | solution 1 for ULHC.T.layerAccT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:46.141504+00:00
-- url     : https://prove2.me/submissions/8c7f6c61-2718-4d3e-8add-8c8fdbc53334

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
import Theorems.Thm_ULHC_T_nbrT_time_le
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
import Theorems.Thm_ULHC_T_degT_time
import Theorems.Thm_ULHC_T_filterT_time_le
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
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) :
    ∀ k, (layerAccT V F k).time ≤ layerAccCost V F k
  | 0 => by
    have := filterT_time_le (fun z => (do
      let d ← degT F z
      tick 2
      pure ((Black z : Bool) && (d < 2 : Bool)) : TimeM Bool)) V 10
      (fun z _ => by simp [degT_time])
    simp only [layerAccT, time_bind, time_pure, layerAccCost]
    omega
  | k + 1 => by
    have ih := solution V F k
    simp only [layerAccT, layerAccCost, time_bind, layerAccT_ret]
    rw [layerAcc_eq]
    simp only [time_bind, time_tick, time_pure, biUnionT, unionT]
    have hs : ∑ u ∈ layer V F k, ((nbrT V F u).time + (nbrT V F u).ret.card + 1) ≤
        ∑ u ∈ layer V F k, (nbrCost + (nbr V F u).card) :=
      Finset.sum_le_sum (fun u _ => by
        have := nbrT_time_le V F u; rw [nbrT_ret]; unfold nbrCost; omega)
    have he : ((layer V F k).biUnion fun u => (nbrT V F u).ret).card =
        ((layer V F k).biUnion (nbr V F)).card := by simp
    omega
end ULHC.T
