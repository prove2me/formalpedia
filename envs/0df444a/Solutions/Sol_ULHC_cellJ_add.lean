-- Prove2me | solution 1 for ULHC.cellJ_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:53.024587+00:00
-- url     : https://prove2.me/submissions/52c69a7f-35ff-4e4d-9deb-a540deb36e81

import Definitions.Def_ULHC_NearGeo
import Definitions.Def_ULHC_NearChain
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
theorem _root_.solution (z : Pt) (tf : Side) (i j : ℕ) : cellJ (cellJ z tf i) tf j = cellJ z tf (i + j) := by
  obtain ⟨x, y⟩ := z
  cases tf <;> simp only [cellJ, Nat.cast_add] <;> ring_nf
end ULHC
