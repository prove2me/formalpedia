-- Prove2me | solution 1 for ULHC.back1_ne_front1_nb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:34:39.157878+00:00
-- url     : https://prove2.me/submissions/46be97f1-a2bd-4003-9591-0423fa4a642a

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
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
theorem _root_.solution (d : Pt) (s : Side) : back1 d s ≠ front1 (nb d s) s := by
  obtain ⟨x, y⟩ := d; cases s <;> simp [back1, front1, nb] <;> omega
end ULHC
