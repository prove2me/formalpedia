-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_extension_ws
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:29:33.803122+00:00
-- url     : https://prove2.me/submissions/941233af-f02e-49c0-8840-a3606e810aa8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_ws
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_ws

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_ws L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_graph_edge_count_ws M hM hcard hmax⟩