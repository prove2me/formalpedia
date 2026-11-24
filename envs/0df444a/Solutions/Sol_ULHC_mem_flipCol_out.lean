-- Prove2me | solution 1 for ULHC.mem_flipCol_out
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:17:03.603866+00:00
-- url     : https://prove2.me/submissions/b034219d-3a01-40c7-8fc7-9eaad5cd26f2

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_mem_flipCol
import Theorems.Thm_ULHC_nOn_eq
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {F : Finset Edge} {c : Pt} {s : Side} {n : ℕ} {e : Edge}
    (h : ∀ j < n, e ∉ cellE (cellJ c s j)) : e ∈ flipCol F c s n ↔ e ∈ F := by
  rw [mem_flipCol, nOn_eq c s n e ∅ (fun j hj => by simp [h j hj]) (by simp)]
  simp
end ULHC
