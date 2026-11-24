-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_supergraph_with_edge_bound__p2m_a3d46af7_d8d1_44e5_ae3d_980c06c923f9_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:42:17.465149+00:00
-- url     : https://prove2.me/submissions/7d88372e-1bc4-4f38-aecb-2140c503c333

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Set V) [Fintype S]
    (G : SimpleGraph S)
    (hDraw : HasPlanarDrawingOn G)
    (hcard : 3 ≤ S.ncard) :
    ∃ N : SimpleGraph S, G ≤ N ∧ HasPlanarDrawingOn N ∧
      3 * S.ncard ≤ N.edgeSet.ncard + 6 := by
  have hs : S.ncard = Fintype.card S := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  obtain ⟨N, hGN, hN, -, h⟩ := WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc G (by omega) hDraw
  exact ⟨N, hGN, hN, by omega⟩
