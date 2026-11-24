-- Prove2me | solution 1 for ULHC.twoFactor_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:01:25.509816+00:00
-- url     : https://prove2.me/submissions/b1b3b5e1-50cf-46e6-b756-4e80ee1e3e8d

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_stuck_full
import Theorems.Thm_ULHC_TF_augLoop_final
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
open TF
namespace ULHC
theorem _root_.solution {V : Finset Pt} (h : twoFactor V = none) : ¬ ∃ F, Deg2 V F := by
  dsimp only [twoFactor] at h
  split_ifs at h with hall
  rintro ⟨G, hG⟩
  exact hall (stuck_full (augLoop_final V).1 (augLoop_final V).2 hG)
end ULHC
