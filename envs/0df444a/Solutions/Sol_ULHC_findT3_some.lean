-- Prove2me | solution 1 for ULHC.findT3_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:59:44.529086+00:00
-- url     : https://prove2.me/submissions/d40434e5-2822-43a1-8d0b-0bd375e3389a

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
import Theorems.Thm_ULHC_mem_cellList
import Theorems.Thm_ULHC_t3B_iff
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
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} (hGV : Inside V G) {d : Pt} {tf : Side}
    (h : findT3 V G = some (d, tf)) : IsCell V d ∧ back d tf ∈ G ∧ front d tf ∈ G ∧
      lat1 d tf ∉ G ∧ lat2 d tf ∉ G ∧ ¬ Conn G (back1 d tf) (front1 d tf) := by
  unfold findT3 at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [List.mem_flatMap, List.mem_map] at hm
  obtain ⟨d', hd', t', _, he⟩ := hm
  cases he
  have hc := (mem_cellList.1 hd').2
  exact ⟨hc, (t3B_iff hGV hc).1 hp⟩
end ULHC
