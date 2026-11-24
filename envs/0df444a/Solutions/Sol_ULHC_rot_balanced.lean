-- Prove2me | solution 1 for ULHC.rot_balanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:56:15.211284+00:00
-- url     : https://prove2.me/submissions/6bb868ff-8c9f-467f-bc17-c8be2d59b614

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
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
theorem _root_.solution {f : Edge → ℤ} (h : ∀ x, outflow f x = 0) : Balanced (rot f) := by
  intro x
  have := h x
  unfold outflow at this
  simp only [eD, eR, eL, eU] at this
  simp only [rot, eD, eR, eL, eU]
  linarith
end ULHC
