-- Prove2me | solution 1 for ULHC.start_corner_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:17:52.938193+00:00
-- url     : https://prove2.me/submissions/90041d3e-85db-4800-bc7a-a2d14eae3a5d

import Definitions.Def_ULHC_NearChain
import Definitions.Def_ULHC_NearLemma
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
theorem _root_.solution {F : Finset Edge} {w : StripSpec} (hp : StripPat F w.c w.s w.n)
    (h1 : 1 ≤ w.n) :
    (back w.c w.s ∈ F ∧ ((back w.c w.s).p = back1 w.c w.s ∨ (back w.c w.s).q = back1 w.c w.s) ∧
      back w.c w.s ∈ cellE (cellJ w.c w.s 0)) ∧
    ∃ j < w.n, ∃ x ∈ F, (x.p = front1 w.c w.s ∨ x.q = front1 w.c w.s) ∧
      x ∈ cellE (cellJ w.c w.s j) := by
  refine ⟨⟨hp.1, (ends_back w.c w.s).inc_iff _ |>.2 (Or.inl rfl), by
    rw [cellJ_zero, cellE_frame w.c w.s]; simp⟩, ?_⟩
  by_cases hn : w.n = 1
  · refine ⟨0, by omega, front w.c w.s, ?_, (ends_front w.c w.s).inc_iff _ |>.2 (Or.inl rfl), ?_⟩
    · have := hp.2.2 0 (by omega); rw [cellJ_zero] at this; rw [this]; omega
    · rw [cellJ_zero, cellE_frame w.c w.s]; simp
  · refine ⟨1, by omega, lat1 (cellJ w.c w.s 1) w.s, (hp.2.1 1 (by omega)).1.2 rfl, ?_, ?_⟩
    · have he := ends_lat1 (cellJ w.c w.s 1) w.s
      rw [← nb_cellJ, cellJ_zero, back1_nb] at he
      rw [← nb_cellJ, cellJ_zero]
      exact he.inc_iff _ |>.2 (Or.inl rfl)
    · rw [cellE_frame _ w.s]; simp
end ULHC
