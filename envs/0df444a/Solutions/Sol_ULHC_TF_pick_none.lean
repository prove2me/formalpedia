-- Prove2me | solution 1 for ULHC.TF.pick_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:56.602581+00:00
-- url     : https://prove2.me/submissions/4e96333d-6bee-47b9-ba96-ba658bd85e91

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
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
theorem _root_.solution {S : Finset Pt} (h : pick S = none) : S = ∅ := by
  unfold pick at h
  split at h
  · rename_i hx
    exact image_eq_empty.1 (Finset.min_eq_top.1 hx)
  · exact absurd h (by simp)
end ULHC.TF
