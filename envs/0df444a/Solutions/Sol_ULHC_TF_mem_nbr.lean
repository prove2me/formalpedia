-- Prove2me | solution 1 for ULHC.TF.mem_nbr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:12.639145+00:00
-- url     : https://prove2.me/submissions/c7f74067-714e-4687-9411-ad0af458b50b

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_mem_inc4
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
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {u v : Pt} :
    v ∈ nbr V F u ↔ ∃ e, (e.p = u ∨ e.q = u) ∧ Fwd V F u e ∧ other e u = v := by
  simp [nbr, mem_inc4, and_assoc]
end ULHC.TF
