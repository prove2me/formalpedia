-- Prove2me | solution 3 for WilliamsonShmoys.planar_disconnected_has_strict_supergraph_of_three_vertices
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:47:37.779966+00:00
-- url     : https://prove2.me/submissions/7af4d424-a157-4891-99b3-571b6cc81cf2

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
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨J, h1, h2, h3⟩ := WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing G hG hV hDisconnected
  exact ⟨J, lt_of_le_of_ne h1 (Ne.symm h2), h3⟩
