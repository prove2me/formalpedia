-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_with_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:57:39.695508+00:00
-- url     : https://prove2.me/submissions/2f50f5d8-1fce-4747-b5f5-27b4af76111d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_has_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_has_maximal_extension G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count K hK hcard hmax⟩