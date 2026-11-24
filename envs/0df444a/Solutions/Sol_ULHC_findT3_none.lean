-- Prove2me | solution 1 for ULHC.findT3_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:13:38.171673+00:00
-- url     : https://prove2.me/submissions/1d932e2a-0ade-4f4f-8aed-3b7fe678062e

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
import Theorems.Thm_ULHC_mem_cellList
import Theorems.Thm_ULHC_mem_sidesL
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
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} (hGV : Inside V G) (h : findT3 V G = none) :
    NoTypeIII V G := by
  intro d hd tf hb hf hl1 hl2
  by_contra hn
  unfold findT3 at h
  have := List.find?_eq_none.1 h (d, tf) (by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨d, mem_cellList.2 ⟨hd.1, hd⟩, tf, mem_sidesL tf, rfl⟩)
  exact this ((t3B_iff hGV hd).2 ⟨hb, hf, hl1, hl2, hn⟩)
end ULHC
