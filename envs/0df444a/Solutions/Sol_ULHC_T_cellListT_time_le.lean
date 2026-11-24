-- Prove2me | solution 1 for ULHC.T.cellListT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:14.66569+00:00
-- url     : https://prove2.me/submissions/6dd0c901-c5a7-4edd-bfac-10d38555d068

import Definitions.Def_ULHC_Timed_Strips
import Definitions.Def_ULHC_Timed_MinPath
import Definitions.Def_ULHC_Timed_TwoFactor
import Definitions.Def_ULHC_CostAlg
import Definitions.Def_ULHC_Timed_Alg
import Theorems.Thm_ULHC_T_cellListT_ret
import Theorems.Thm_ULHC_T_t3BT_ret
import Theorems.Thm_ULHC_T_findT3T_ret
import Theorems.Thm_ULHC_T_decodeT_ret
import Theorems.Thm_ULHC_T_findPathT_ret
import Theorems.Thm_ULHC_T_flipColT_ret
import Theorems.Thm_ULHC_T_roundT_ret
import Theorems.Thm_ULHC_T_runT_ret
import Theorems.Thm_ULHC_T_ulhcT_ret
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_T_allStripsT_ret
import Theorems.Thm_ULHC_T_aminT_ret
import Theorems.Thm_ULHC_T_augLoopT_ret
import Theorems.Thm_ULHC_T_augStepT_ret
import Theorems.Thm_ULHC_T_bwdT_ret
import Theorems.Thm_ULHC_T_candNT_ret
import Theorems.Thm_ULHC_T_candT_ret
import Theorems.Thm_ULHC_T_cclsT_ret
import Theorems.Thm_ULHC_T_chainOKBT_ret
import Theorems.Thm_ULHC_T_cncompT_ret
import Theorems.Thm_ULHC_T_connBT_ret
import Theorems.Thm_ULHC_T_cr2BT_ret
import Theorems.Thm_ULHC_T_creachT_ret
import Theorems.Thm_ULHC_T_degT_ret
import Theorems.Thm_ULHC_T_endOffBT_ret
import Theorems.Thm_ULHC_T_filterT_time_le
import Theorems.Thm_ULHC_T_flipT_ret
import Theorems.Thm_ULHC_T_fnbrT_ret
import Theorems.Thm_ULHC_T_fwdT_ret
import Theorems.Thm_ULHC_T_gedgeT_ret
import Theorems.Thm_ULHC_T_gsrcT_ret
import Theorems.Thm_ULHC_T_isCellT_ret
import Theorems.Thm_ULHC_T_isCellT_time
import Theorems.Thm_ULHC_T_latOKT_ret
import Theorems.Thm_ULHC_T_layerAccT_ret
import Theorems.Thm_ULHC_T_layerT_ret
import Theorems.Thm_ULHC_T_lmapT_time_le
import Theorems.Thm_ULHC_T_lookT_ret
import Theorems.Thm_ULHC_T_midBT_ret
import Theorems.Thm_ULHC_T_minPathLT_ret
import Theorems.Thm_ULHC_T_minPathT_ret
import Theorems.Thm_ULHC_T_nbrT_ret
import Theorems.Thm_ULHC_T_nextT_ret
import Theorems.Thm_ULHC_T_notEndBT_ret
import Theorems.Thm_ULHC_T_pickSrcT_ret
import Theorems.Thm_ULHC_T_predT_ret
import Theorems.Thm_ULHC_T_ret_bind
import Theorems.Thm_ULHC_T_ret_pure
import Theorems.Thm_ULHC_T_ret_tick
import Theorems.Thm_ULHC_T_sideOffBT_ret
import Theorems.Thm_ULHC_T_stepT_ret
import Theorems.Thm_ULHC_T_stripLenT_ret
import Theorems.Thm_ULHC_T_stripScanT_ret
import Theorems.Thm_ULHC_T_time_bind
import Theorems.Thm_ULHC_T_time_pure
import Theorems.Thm_ULHC_T_time_tick
import Theorems.Thm_ULHC_T_twoFactorT_ret
import Theorems.Thm_ULHC_T_validBT_ret
import Theorems.Thm_ULHC_T_walkT_ret
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v
attribute [local simp] ULHC.T.allStripsT_ret
attribute [local simp] ULHC.T.aminT_ret
attribute [local simp] ULHC.T.augLoopT_ret
attribute [local simp] ULHC.T.augStepT_ret
attribute [local simp] ULHC.T.bwdT_ret
attribute [local simp] ULHC.T.candNT_ret
attribute [local simp] ULHC.T.candT_ret
attribute [local simp] ULHC.T.cclsT_ret
attribute [local simp] ULHC.T.chainOKBT_ret
attribute [local simp] ULHC.T.cncompT_ret
attribute [local simp] ULHC.T.connBT_ret
attribute [local simp] ULHC.T.cr2BT_ret
attribute [local simp] ULHC.T.creachT_ret
attribute [local simp] ULHC.T.degT_ret
attribute [local simp] ULHC.T.endOffBT_ret
attribute [local simp] ULHC.T.flipT_ret
attribute [local simp] ULHC.T.fnbrT_ret
attribute [local simp] ULHC.T.fwdT_ret
attribute [local simp] ULHC.T.gedgeT_ret
attribute [local simp] ULHC.T.gsrcT_ret
attribute [local simp] ULHC.T.isCellT_ret
attribute [local simp] ULHC.T.latOKT_ret
attribute [local simp] ULHC.T.layerAccT_ret
attribute [local simp] ULHC.T.layerT_ret
attribute [local simp] ULHC.T.lookT_ret
attribute [local simp] ULHC.T.midBT_ret
attribute [local simp] ULHC.T.minPathLT_ret
attribute [local simp] ULHC.T.minPathT_ret
attribute [local simp] ULHC.T.nbrT_ret
attribute [local simp] ULHC.T.nextT_ret
attribute [local simp] ULHC.T.notEndBT_ret
attribute [local simp] ULHC.T.pickSrcT_ret
attribute [local simp] ULHC.T.predT_ret
attribute [local simp] ULHC.T.ret_bind
attribute [local simp] ULHC.T.ret_pure
attribute [local simp] ULHC.T.ret_tick
attribute [local simp] ULHC.T.sideOffBT_ret
attribute [local simp] ULHC.T.stepT_ret
attribute [local simp] ULHC.T.stripLenT_ret
attribute [local simp] ULHC.T.stripScanT_ret
attribute [local simp] ULHC.T.time_bind
attribute [local simp] ULHC.T.time_pure
attribute [local simp] ULHC.T.time_tick
attribute [local simp] ULHC.T.twoFactorT_ret
attribute [local simp] ULHC.T.validBT_ret
attribute [local simp] ULHC.T.walkT_ret


attribute [local simp] ULHC.T.cellListT_ret
attribute [local simp] ULHC.T.t3BT_ret
attribute [local simp] ULHC.T.findT3T_ret
attribute [local simp] ULHC.T.decodeT_ret
attribute [local simp] ULHC.T.findPathT_ret
attribute [local simp] ULHC.T.flipColT_ret
attribute [local simp] ULHC.T.roundT_ret
attribute [local simp] ULHC.T.runT_ret
attribute [local simp] ULHC.T.ulhcT_ret

set_option autoImplicit true
open ULHC ULHC.T
open Finset
namespace ULHC.T
theorem _root_.solution (V : Finset Pt) : (cellListT V).time ≤ cellListCost V := by
  have h1 := filterT_time_le (isCellT V) V 7 (fun x _ => (isCellT_time V x).le)
  set Cs := (filterT (isCellT V) V).ret
  have hCs : Cs.card ≤ V.card := by simp only [Cs, filterT]; exact card_filter_le _ _
  have h2 : (imageT (fun x => (pure (toLex x) : TimeM (Lex (ℤ × ℤ)))) Cs).time ≤ Cs.card := by
    simp [imageT]
  have hLs : (imageT (fun x => (pure (toLex x) : TimeM (Lex (ℤ × ℤ)))) Cs).ret.card ≤ V.card := by
    simp only [imageT, ret_pure]; exact card_image_le.trans hCs
  have h3 := Nat.pow_le_pow_left hLs 2
  set Ls := (imageT (fun x => (pure (toLex x) : TimeM (Lex (ℤ × ℤ)))) Cs).ret
  have h4 := lmapT_time_le (fun x => (pure (ofLex x) : TimeM Pt)) (Ls.sort (· ≤ ·)) 0 (fun _ _ => le_rfl)
  rw [Finset.length_sort] at h4
  simp only [cellListT, time_bind, sortT, cellListCost]
  nlinarith
end ULHC.T
