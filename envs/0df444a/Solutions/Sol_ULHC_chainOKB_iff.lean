-- Prove2me | solution 1 for ULHC.chainOKB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:57:14.372158+00:00
-- url     : https://prove2.me/submissions/83a74349-3d25-459b-9b5a-461df68dcaa7

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
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
namespace ULHC
theorem _root_.solution {b c : StripSpec} : chainOKB b c = true ↔ ChainOK b c := by
  simp only [chainOKB, ChainOK, List.all_eq_true, List.mem_range, decide_eq_true_eq]
end ULHC
