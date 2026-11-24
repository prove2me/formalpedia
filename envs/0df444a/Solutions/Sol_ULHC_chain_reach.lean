-- Prove2me | solution 1 for ULHC.chain_reach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:38.459513+00:00
-- url     : https://prove2.me/submissions/61935599-1c1e-461c-a212-571b1943fba1

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
import Theorems.Thm_ULHC_Conn_refl
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
theorem _root_.solution {r : Pt → Pt → Prop} {u : Pt} {l : List Pt} (h : List.IsChain r (u :: l))
    {z : Pt} (hz : z ∈ u :: l) : Relation.ReflTransGen r u z := by
  induction l generalizing u with
  | nil =>
    simp at hz; subst hz; exact Relation.ReflTransGen.refl
  | cons v l ih =>
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.1 hz with hz | hz
    · subst hz; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head h.1 (ih h.2 hz)
end ULHC
