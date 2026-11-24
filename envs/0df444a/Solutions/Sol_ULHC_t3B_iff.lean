-- Prove2me | solution 1 for ULHC.t3B_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:58:03.790034+00:00
-- url     : https://prove2.me/submissions/e1289e01-5b58-4f0d-a4d0-28ba6ce6536d

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_bool_not_iff
import Theorems.Thm_ULHC_connB_iff
import Theorems.Thm_ULHC_corners4
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {G : Finset Edge} (hGV : Inside V G) {d : Pt} (hd : IsCell V d)
    {tf : Side} : t3B V G d tf = true ↔ back d tf ∈ G ∧ front d tf ∈ G ∧ lat1 d tf ∉ G ∧
      lat2 d tf ∉ G ∧ ¬ Conn G (back1 d tf) (front1 d tf) := by
  obtain ⟨hb, _, hf, _⟩ := corners4 hd tf
  unfold t3B
  simp only [Bool.and_eq_true, decide_eq_true_eq, bool_not_iff (connB_iff hGV hb hf)]
  tauto
end ULHC
