-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulating_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:26:24.145857+00:00
-- url     : https://prove2.me/submissions/85148052-19fe-4398-b558-36906de9fff2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph_maximal_extension
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulating_supergraph_maximal_extension N hV hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.drawable_graph_has_triangulating_supergraph_maximal_edge_count K hV hK hmax⟩