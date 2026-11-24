-- Prove2me | solution 1 for ULHC.TF.augStep_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:46.42547+00:00
-- url     : https://prove2.me/submissions/5c83e08c-8229-457f-bad3-cc6e4125c93b

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_layerAcc_eq
import Theorems.Thm_ULHC_TF_pick_none
import Theorems.Thm_ULHC_ACell_split
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



set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (h : augStep V F = none)
    {w : Pt} (hw : w ∈ layer V F V.card) (hwb : ¬ Black w) : ¬ deg F w < 2 := by
  unfold augStep at h
  rw [layerAcc_eq] at h
  simp only at h
  split at h
  · rename_i hp
    have := pick_none hp
    intro hd
    have hm : w ∈ (layer V F V.card).filter (fun w => ¬ Black w ∧ deg F w < 2) :=
      mem_filter.2 ⟨hw, hwb, hd⟩
    rw [this] at hm
    exact absurd hm (Finset.notMem_empty w)
  · exact absurd h (by simp)
end ULHC.TF
