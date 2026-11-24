-- Prove2me | solution 1 for ULHC.TF.other_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:45:46.234924+00:00
-- url     : https://prove2.me/submissions/62f567e8-054d-4730-8056-d8ee4e8fd37e

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_p_ne_q
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
theorem _root_.solution {e : Edge} {v : Pt} (hv : e.p = v ∨ e.q = v) : other e (other e v) = v := by
  have hne := e.p_ne_q
  unfold other
  by_cases h : e.p = v
  · subst h; simp [hne]
  · have hq : e.q = v := hv.resolve_left h
    subst hq; simp [h]
end ULHC.TF
