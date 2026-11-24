-- Prove2me | solution 1 for ULHC.besideA_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:02:26.344571+00:00
-- url     : https://prove2.me/submissions/a5c8a97c-c392-46bb-b9f3-00737bae7c71

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
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
theorem _root_.solution (c : Pt) (s : Side) (m j i : ℕ) :
    cellJ (nb (cellJ c s m) (latA s)) s j ≠ cellJ c s i := by
  obtain ⟨p, q⟩ := c; cases s <;> simp [nb, latA, cellJ]
end ULHC
