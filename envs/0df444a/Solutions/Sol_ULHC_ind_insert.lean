-- Prove2me | solution 1 for ULHC.ind_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:11.549739+00:00
-- url     : https://prove2.me/submissions/0e618cf7-019f-4465-9b69-c916a18aded4

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_PStep_symm
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {e : Edge} {B : Finset Edge} (he : e ∉ B) (f : Edge) :
    ind (insert e B) f = ind B f + if e = f then 1 else 0 := by
  unfold ind
  by_cases h : e = f
  · subst h; simp [he]
  · have : f ≠ e := fun h' => h h'.symm
    simp [Finset.mem_insert, this, h]
end ULHC
