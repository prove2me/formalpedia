-- Prove2me | solution 1 for ULHC.closed_cls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:52.584094+00:00
-- url     : https://prove2.me/submissions/8d06ac97-eea2-420f-9b08-591631a92f94

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_Conn_of_adj
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
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hV : Inside V F) (x : Pt) :
    Closed F (cls V F x) := by
  intro y hy z hz
  unfold cls at hy ⊢
  simp only [Finset.mem_filter] at hy ⊢
  obtain ⟨f, hf, h⟩ := hz
  refine ⟨?_, hy.2.trans (Conn.of_adj ⟨f, hf, h⟩)⟩
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · rw [← h]; exact (hV f hf).2
  · rw [← h]; exact (hV f hf).1
end ULHC
