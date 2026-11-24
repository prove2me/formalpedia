-- Prove2me | solution 1 for ULHC.sideOffB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:59:47.818813+00:00
-- url     : https://prove2.me/submissions/2df59780-f8ed-48c3-91b3-42ee935284e7

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
theorem _root_.solution {b c : StripSpec} : sideOffB b c = true ↔ SideOff b c := by
  simp only [sideOffB, SideOff, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h j hj i hi e he; exact h j hj i (by omega) e he
  · intro h j hj i hi e he; exact h j hj i (by omega) e he
end ULHC
