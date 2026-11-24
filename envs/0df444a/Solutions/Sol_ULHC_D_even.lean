-- Prove2me | solution 1 for ULHC.D_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:04.505803+00:00
-- url     : https://prove2.me/submissions/e3cf4409-deed-421f-8023-e1e5cf041e9d

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
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
theorem _root_.solution (F H : Finset Edge) (c : Pt) : 2 ∣ D F H c := by
  unfold D pot
  apply Finset.dvd_sum
  intro e _
  unfold wD wb
  split_ifs <;> simp
end ULHC
