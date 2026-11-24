-- Prove2me | solution 1 for ULHC.T.allStripsT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:50.355427+00:00
-- url     : https://prove2.me/submissions/c239175f-f395-4558-9a84-07c9b3586ee9

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
import Theorems.Thm_ULHC_T_stripLenT_time_le
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_T_card_optStrips_le
import Theorems.Thm_ULHC_T_cclsT_ret
import Theorems.Thm_ULHC_T_cncompT_ret
import Theorems.Thm_ULHC_T_connBT_ret
import Theorems.Thm_ULHC_T_creachT_ret
import Theorems.Thm_ULHC_T_degT_ret
import Theorems.Thm_ULHC_T_filterT_time_le
import Theorems.Thm_ULHC_T_fnbrT_ret
import Theorems.Thm_ULHC_T_fsum_le
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
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) :
    (allStripsT V F).time ≤ allStripsCost V F := by
  set inner : Pt → TimeM (Finset StripSpec) := fun c => biUnionT (fun s => do
      let o ← stripLenT V F c s
      pure (optStrips c s o)) sidesF with hinner
  have hin : ∀ c, (inner c).time ≤ ∑ s ∈ sidesF, (stripLenCost V F c s + 2) := by
    intro c
    simp only [hinner, biUnionT, time_bind, time_pure, ret_bind, ret_pure]
    exact Finset.sum_le_sum (fun s _ => by
      have := stripLenT_time_le V F c s
      have := card_optStrips_le c s (stripLenT V F c s).ret
      omega)
  have hcard : ∀ c, (inner c).ret.card ≤ 4 := by
    intro c
    simp only [hinner, biUnionT, ret_bind, ret_pure]
    refine card_biUnion_le.trans ?_
    have := fsum_le sidesF (fun s => (optStrips c s (stripLenT V F c s).ret).card) 1
      (fun s _ => card_optStrips_le _ _ _)
    have hs : sidesF.card = 4 := by decide
    omega
  have hf : (filterT (isCellT V) V).ret = V.filter (IsCell V) := by
    simp only [filterT, isCellT_ret, decide_eq_true_eq]
  have e1 : (allStripsT V F).time =
      (filterT (isCellT V) V).time + (biUnionT inner (filterT (isCellT V) V).ret).time := rfl
  have hfc := filterT_time_le (isCellT V) V 7 (fun x _ => (isCellT_time V x).le)
  have e2 : (biUnionT inner (V.filter (IsCell V))).time =
      ∑ c ∈ V.filter (IsCell V), ((inner c).time + (inner c).ret.card + 1) := rfl
  have h2 : ∑ c ∈ V.filter (IsCell V), ((inner c).time + (inner c).ret.card + 1) ≤
      ∑ c ∈ V.filter (IsCell V), (∑ s ∈ sidesF, (stripLenCost V F c s + 2) + 5) :=
    Finset.sum_le_sum (fun c _ => by have := hin c; have := hcard c; omega)
  have e3 : ∑ _c ∈ V, 8 = V.card * 8 := by simp
  rw [e1, hf, e2]
  unfold allStripsCost
  omega
end ULHC.T
