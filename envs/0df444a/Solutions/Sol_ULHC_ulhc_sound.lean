-- Prove2me | solution 1 for ULHC.ulhc_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:23:12.112799+00:00
-- url     : https://prove2.me/submissions/8de7e286-d76a-45bb-9a84-03457d25c1a5

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
import Theorems.Thm_ULHC_run_sound
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_twoFactor_some
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} (h : ulhc V = true) : ∃ H, Deg2 V H ∧ ncomp V H = 1 := by
  unfold ulhc at h
  rcases hf : twoFactor V with _ | F
  · rw [hf] at h; simp at h
  · rw [hf] at h
    exact run_sound _ F (twoFactor_some hf) h
end ULHC
