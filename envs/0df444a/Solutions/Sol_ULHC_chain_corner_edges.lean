-- Prove2me | solution 1 for ULHC.chain_corner_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:18:00.009675+00:00
-- url     : https://prove2.me/submissions/a8e7d5cb-3806-41d7-8558-27a92cb0ba48

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_back1_nb
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_nb_cellJ
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {F : Finset Edge} {w : StripSpec} (h1 : 1 ≤ w.n)
    (hb : back w.c w.s ∈ F) (hfr : front w.c w.s ∈ F ↔ w.n = 1)
    (hzs : SigFrom F w.c w.s w.n 1) :
    (back w.c w.s ∈ F ∧ ((back w.c w.s).p = back1 w.c w.s ∨ (back w.c w.s).q = back1 w.c w.s) ∧
      back w.c w.s ∈ cellE (cellJ w.c w.s 0)) ∧
    ∃ j < w.n, ∃ x ∈ F, (x.p = front1 w.c w.s ∨ x.q = front1 w.c w.s) ∧
      x ∈ cellE (cellJ w.c w.s j) := by
  refine ⟨⟨hb, (ends_back w.c w.s).inc_iff _ |>.2 (Or.inl rfl), by
    rw [cellJ_zero, cellE_frame w.c w.s]; simp⟩, ?_⟩
  by_cases hn : w.n = 1
  · refine ⟨0, by omega, front w.c w.s, hfr.2 hn, (ends_front w.c w.s).inc_iff _ |>.2 (Or.inl rfl),
      ?_⟩
    rw [cellJ_zero, cellE_frame w.c w.s]; simp
  · refine ⟨1, by omega, lat1 (cellJ w.c w.s 1) w.s, (hzs 1 le_rfl (by omega)).1.2 rfl, ?_, ?_⟩
    · have he := ends_lat1 (cellJ w.c w.s 1) w.s
      rw [← nb_cellJ, cellJ_zero, back1_nb] at he
      rw [← nb_cellJ, cellJ_zero]
      exact he.inc_iff _ |>.2 (Or.inl rfl)
    · rw [cellE_frame _ w.s]; simp
end ULHC
