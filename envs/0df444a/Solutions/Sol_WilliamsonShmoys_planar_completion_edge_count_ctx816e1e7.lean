-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count_ctx816e1e7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:27:21.296498+00:00
-- url     : https://prove2.me/submissions/3a546a1c-5b19-4b61-a6b9-5e8b89927939
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_ctx816e1e7
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph_ctx816e1e7

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨R, hQR, hR, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_ctx816e1e7 Q hQ
  refine ⟨R, hQR, hR, ?_⟩
  exact WilliamsonShmoys.edge_count_of_maximal_planar_graph_ctx816e1e7
    R hV hR hmax