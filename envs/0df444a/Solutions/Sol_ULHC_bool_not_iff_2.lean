-- Prove2me | solution 2 for ULHC.bool_not_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:51:40.329566+00:00
-- url     : https://prove2.me/submissions/dc307f63-400b-4996-9a6b-b893f9746433

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
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
variable {V : Finset Pt} {F G : Finset Edge}
namespace ULHC
theorem _root_.solution {p : Bool} {P : Prop} (h : p = true ↔ P) : (!p) = true ↔ ¬ P := by
  rw [Bool.not_eq_true', ← h]; cases p <;> simp
end ULHC
