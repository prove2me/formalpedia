-- Prove2me | solution 1 for ULHC.TF.augStep_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:54:59.142418+00:00
-- url     : https://prove2.me/submissions/c5aad48c-216b-4eff-a9b9-fa40ebf10965

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_layerAcc_eq
import Theorems.Thm_ULHC_TF_walk_spec
import Theorems.Thm_ULHC_TF_pick_some
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
theorem _root_.solution {V : Finset Pt} {F F' : Finset Edge} (hF : Good V F)
    (h : augStep V F = some F') : Good V F' ∧ F'.card = F.card + 1 := by
  unfold augStep at h
  rw [layerAcc_eq] at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i w hw
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hwL, hwb, hwd⟩ := mem_filter.1 (pick_some hw)
    exact walk_spec hF _ w F
      ⟨hwL, hF.1, fun z _ => hF.2 z, fun _ => ⟨hwd, rfl⟩, fun h => absurd h hwb,
        fun _ _ _ => rfl, fun _ => Or.inl Iff.rfl⟩
end ULHC.TF
