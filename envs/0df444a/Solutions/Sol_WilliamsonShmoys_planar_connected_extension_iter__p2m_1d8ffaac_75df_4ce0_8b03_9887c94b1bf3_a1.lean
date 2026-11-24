-- Prove2me | solution 1 for WilliamsonShmoys_planar_connected_extension_iter__p2m_1d8ffaac_75df_4ce0_8b03_9887c94b1bf3_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:17.770645+00:00
-- url     : https://prove2.me/submissions/946660cd-18d4-4b41-b501-c11b245e96de

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_strict_extension

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hstep : ∀ (K : SimpleGraph V), H ≤ K → HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ L : SimpleGraph V, ∃ u v : V,
        K ≤ L ∧ HasPlanarDrawingOn L ∧ ¬ K.Reachable u v ∧ L.Adj u v) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Connected := by
  obtain ⟨C, hGC, ⟨-, hC⟩, hconnC⟩ := WilliamsonShmoys.exists_connected_supergraph_of_strict_extension H
    (fun X => H ≤ X ∧ HasPlanarDrawingOn X) ⟨le_rfl, hH⟩ (by
      rintro K - ⟨hHK, hK⟩ hnc
      obtain ⟨L, u, v, hKL, hL, hnr, hLuv⟩ := hstep K hHK hK hnc
      refine ⟨L, lt_of_le_of_ne hKL ?_, hHK.trans hKL, hL⟩
      intro hEq
      rw [← hEq] at hLuv
      exact hnr hLuv.reachable)
  exact ⟨C, hGC, hC, hconnC⟩
