-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulation_extension_for_maximality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:49:39.434348+00:00
-- url     : https://prove2.me/submissions/54b9c100-e8f3-4d12-a7de-c2bc6dde7c01
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_edge_maximal_extension_719c6bb7_9aa0_4725_9f39_6c34f4357440
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_has_euler_edge_count_719c6bb7_9aa0_4725_9f39_6c34f4357440

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_edge_maximal_extension_719c6bb7_9aa0_4725_9f39_6c34f4357440 L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.edge_maximal_planar_drawing_has_euler_edge_count_719c6bb7_9aa0_4725_9f39_6c34f4357440 M hV hM hmax⟩