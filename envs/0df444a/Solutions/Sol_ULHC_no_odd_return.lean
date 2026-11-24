-- Prove2me | solution 1 for ULHC.no_odd_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:41:32.49263+00:00
-- url     : https://prove2.me/submissions/dfb57712-83cd-4f29-8563-5d80a554b1c8

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_closed_chain_even
import Theorems.Thm_ULHC_GE_inside
import Theorems.Thm_ULHC_preach_chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
variable (hs : Solid V) (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0)
include hs heven
namespace ULHC
theorem _root_.solution {a : Pt} {b : Bool} :
    ¬ Relation.ReflTransGen (PStep V B) (a, b) (a, !b) := by
  intro h
  obtain ⟨l, hl, hlast, hpar⟩ := preach_chain B h
  have := closed_chain_even hs (GE_inside V) B heven hl hlast
  cases b <;> simp at hpar <;> omega
end ULHC
