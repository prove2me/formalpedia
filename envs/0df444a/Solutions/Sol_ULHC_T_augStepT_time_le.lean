-- Prove2me | solution 1 for ULHC.T.augStepT_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:42:10.430201+00:00
-- url     : https://prove2.me/submissions/d6a85213-fa66-4c80-899d-062e4dec8818

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
import Theorems.Thm_ULHC_T_layerAccT_time_le
import Theorems.Thm_ULHC_T_walkT_time_le
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
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) : (augStepT V F).time ≤ augStepCost V F := by
  have h0 := layerAccT_time_le V F V.card
  simp only [augStepT, augStepCost, time_bind, cardT, layerAccT_ret]
  rw [layerAcc_eq]
  simp only [time_bind, pickT]
  have hfe : (filterT (fun w => (do
      let d ← degT F w
      tick 2
      pure (!(Black w : Bool) && (d < 2 : Bool)) : TimeM Bool)) (layer V F V.card)).ret =
      (layer V F V.card).filter (fun w => ¬ Black w ∧ deg F w < 2) := by
    ext w; simp [filterT]
  have hft : (filterT (fun w => (do
      let d ← degT F w
      tick 2
      pure (!(Black w : Bool) && (d < 2 : Bool)) : TimeM Bool)) (layer V F V.card)).time =
      ∑ _w ∈ layer V F V.card, (degCost + 3) := by
    simp [filterT, degT_time, degCost]
  rw [hft, hfe]
  rcases TF.pick ((layer V F V.card).filter (fun w => ¬ Black w ∧ deg F w < 2)) with _ | w
  · simp only [time_pure]; unfold pickCost; omega
  · simp only [time_bind, time_pure]
    have := walkT_time_le V F (layersBelow V F V.card) w F
    unfold pickCost; omega
end ULHC.T
