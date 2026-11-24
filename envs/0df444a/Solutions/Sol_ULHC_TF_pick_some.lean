-- Prove2me | solution 1 for ULHC.TF.pick_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:55.752271+00:00
-- url     : https://prove2.me/submissions/f3e29f7a-1f4c-429b-9c01-3a61e06b3979

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
theorem _root_.solution {S : Finset Pt} {p : Pt} (h : pick S = some p) : p ∈ S := by
  unfold pick at h
  split at h
  · exact absurd h (by simp)
  · rename_i x hx
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨a, ha, rfl⟩ := mem_image.1 (mem_of_min hx)
    simpa using ha
end ULHC.TF
