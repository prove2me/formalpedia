-- Prove2me | solution 1 for ULHC.cls_eq_of_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:56:36.076094+00:00
-- url     : https://prove2.me/submissions/34e4ee8c-cd21-443a-92ee-d9e91596a283

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
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
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {x y : Pt} (h : Conn F x y) :
    cls V F x = cls V F y := by
  unfold cls; ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz, h'⟩; exact ⟨hz, h.symm.trans h'⟩
  · rintro ⟨hz, h'⟩; exact ⟨hz, h.trans h'⟩
end ULHC
