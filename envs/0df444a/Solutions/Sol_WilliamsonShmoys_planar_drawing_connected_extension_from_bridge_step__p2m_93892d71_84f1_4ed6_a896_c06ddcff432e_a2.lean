-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_from_bridge_step__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:41:18.392799+00:00
-- url     : https://prove2.me/submissions/597a597c-0d0c-4695-a270-b850a3db11af

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

theorem solution {V : Type} [Fintype V] [LinearOrder V] (hStep : ∀ X : SimpleGraph V, ¬ X.Connected → HasPlanarDrawingOn X → ∃ Y : SimpleGraph V, X ≤ Y ∧ HasPlanarDrawingOn Y ∧ ∃ u v : V, ¬ X.Reachable u v ∧ Y.Adj u v) (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hconn : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  obtain ⟨C, hGC, ⟨-, hC⟩, hconnC⟩ := WilliamsonShmoys.exists_connected_supergraph_of_strict_extension G
    (fun X => G ≤ X ∧ HasPlanarDrawingOn X) ⟨le_rfl, hG⟩ (by
      rintro K - ⟨hHK, hK⟩ hnc
      obtain ⟨L, hKL, hL, u, v, hnr, hLuv⟩ := hStep K hnc hK
      refine ⟨L, lt_of_le_of_ne hKL ?_, hHK.trans hKL, hL⟩
      intro hEq
      rw [← hEq] at hLuv
      exact hnr hLuv.reachable)
  exact ⟨C, hGC, hconnC, hC⟩
