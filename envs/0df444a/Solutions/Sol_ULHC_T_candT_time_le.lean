-- Prove2me | solution 1 for ULHC.T.candT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:14.967809+00:00
-- url     : https://prove2.me/submissions/8645a491-efc9-4e17-b5ab-32695380aa92

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
import Theorems.Thm_ULHC_T_latOKT_ret
import Theorems.Thm_ULHC_T_stripScanT_ret
import Theorems.Thm_ULHC_T_stripLenT_ret
import Theorems.Thm_ULHC_T_allStripsT_ret
import Theorems.Thm_ULHC_T_flipT_ret
import Theorems.Thm_ULHC_T_validBT_ret
import Theorems.Thm_ULHC_T_sideOffBT_ret
import Theorems.Thm_ULHC_T_midBT_ret
import Theorems.Thm_ULHC_T_endOffBT_ret
import Theorems.Thm_ULHC_T_notEndBT_ret
import Theorems.Thm_ULHC_T_cr2BT_ret
import Theorems.Thm_ULHC_T_chainOKBT_ret
import Theorems.Thm_ULHC_T_gsrcT_ret
import Theorems.Thm_ULHC_T_gedgeT_ret
import Theorems.Thm_ULHC_T_candT_ret
import Theorems.Thm_ULHC_T_candNT_ret
import Theorems.Thm_ULHC_T_allStripsT_time_le
import Theorems.Thm_ULHC_T_flipT_time_le
import Theorems.Thm_ULHC_APair_flip
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
import Theorems.Thm_ULHC_T_filterT_time_le
import Theorems.Thm_ULHC_T_fnbrT_ret
import Theorems.Thm_ULHC_T_isCellT_ret
import Theorems.Thm_ULHC_T_isCellT_time
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


attribute [local simp] ULHC.T.latOKT_ret
attribute [local simp] ULHC.T.stripScanT_ret
attribute [local simp] ULHC.T.stripLenT_ret
attribute [local simp] ULHC.T.allStripsT_ret
attribute [local simp] ULHC.T.flipT_ret
attribute [local simp] ULHC.T.validBT_ret
attribute [local simp] ULHC.T.sideOffBT_ret
attribute [local simp] ULHC.T.midBT_ret
attribute [local simp] ULHC.T.endOffBT_ret
attribute [local simp] ULHC.T.notEndBT_ret
attribute [local simp] ULHC.T.cr2BT_ret
attribute [local simp] ULHC.T.chainOKBT_ret
attribute [local simp] ULHC.T.gsrcT_ret
attribute [local simp] ULHC.T.gedgeT_ret
attribute [local simp] ULHC.T.candT_ret
attribute [local simp] ULHC.T.candNT_ret

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (V : Finset Pt) (G : Finset Edge) : (candT V G).time ≤ candCost V G := by
  set inner : Pt → TimeM (Finset StripSpec) := fun u => do
    let Gu ← flipT G u
    allStripsT V Gu with hinner
  have hf : (filterT (isCellT V) V).ret = V.filter (IsCell V) := by
    simp only [filterT, isCellT_ret, decide_eq_true_eq]
  have e1 : (candT V G).time = (allStripsT V G).time + ((filterT (isCellT V) V).time +
      ((biUnionT inner (filterT (isCellT V) V).ret).time +
      (unionT (allStripsT V G).ret (biUnionT inner (filterT (isCellT V) V).ret).ret).time)) := rfl
  have h1 := allStripsT_time_le V G
  have hfc := filterT_time_le (isCellT V) V 7 (fun x _ => (isCellT_time V x).le)
  have hret : (biUnionT inner (V.filter (IsCell V))).ret =
      (V.filter (IsCell V)).biUnion (fun u => allStrips V (flip G u)) := by
    simp [hinner, biUnionT]
  have e2 : (biUnionT inner (V.filter (IsCell V))).time =
      ∑ u ∈ V.filter (IsCell V), ((inner u).time + (inner u).ret.card + 1) := rfl
  have h2 : ∑ u ∈ V.filter (IsCell V), ((inner u).time + (inner u).ret.card + 1) ≤
      ∑ u ∈ V.filter (IsCell V), (flipCost + allStripsCost V (flip G u) +
        (allStrips V (flip G u)).card + 1) :=
    Finset.sum_le_sum (fun u _ => by
      have := flipT_time_le G u
      have := allStripsT_time_le V (flip G u)
      have e : (inner u).time = (flipT G u).time + (allStripsT V (flip G u)).time := rfl
      have e' : (inner u).ret = allStrips V (flip G u) := by simp [hinner]
      rw [e, e']
      omega)
  have hA : (allStrips V G).card ≤ (cand V G).card := card_le_card subset_union_left
  have hB : ((V.filter (IsCell V)).biUnion fun u => allStrips V (flip G u)).card ≤
      (cand V G).card := card_le_card subset_union_right
  rw [e1, hf, e2]
  simp only [unionT, allStripsT_ret, hret]
  unfold candCost
  omega
end ULHC.T
