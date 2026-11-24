-- Prove2me | solution 1 for ULHC.twoFactor_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:00:19.868807+00:00
-- url     : https://prove2.me/submissions/889c5084-2fe8-46a9-8c1c-ea9ec28b19ad

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
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
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (h : twoFactor V = some F) :
    Deg2 V F := by
  dsimp only [twoFactor] at h
  split_ifs at h with hall
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨(augLoop_final V).1.1, hall⟩
end ULHC
