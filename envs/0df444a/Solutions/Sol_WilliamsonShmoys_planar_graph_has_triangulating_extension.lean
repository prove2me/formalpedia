-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulating_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:21:08.189072+00:00
-- url     : https://prove2.me/submissions/ede84ba4-962c-4d58-9c4d-fdbd63b660e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_extension_choose_maximal_v4
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count_v4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulating_extension_choose_maximal_v4 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_drawable_supergraph_edge_count_v4 L hV hL hmax⟩