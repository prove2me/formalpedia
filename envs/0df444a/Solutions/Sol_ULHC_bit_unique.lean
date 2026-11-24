-- Prove2me | solution 1 for ULHC.bit_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:43:22.48667+00:00
-- url     : https://prove2.me/submissions/4001730a-4e95-4dc8-a21d-7107582fef0a

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_preach_symm
import Theorems.Thm_ULHC_preach_neg
import Theorems.Thm_ULHC_no_odd_return
import Theorems.Thm_ULHC_Conn_trans
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
theorem _root_.solution {x0 z : Pt} {b1 b2 : Bool}
    (h1 : Relation.ReflTransGen (PStep V B) (x0, false) (z, b1))
    (h2 : Relation.ReflTransGen (PStep V B) (x0, false) (z, b2)) : b1 = b2 := by
  by_contra hne
  have hb : b2 = !b1 := by cases b1 <;> cases b2 <;> simp_all
  have h3 := preach_neg B (preach_symm B h2)
  simp only [hb, Bool.not_not] at h3
  exact no_odd_return B hs heven (h1.trans h3)
end ULHC
