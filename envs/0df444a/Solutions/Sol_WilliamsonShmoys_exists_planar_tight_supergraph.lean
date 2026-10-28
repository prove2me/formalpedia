-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_tight_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:19:06.859768+00:00
-- url     : https://prove2.me/submissions/381da61d-56d5-4437-add6-1b6e137b2241
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_finite_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_from_drawing

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_finite_maximal_extension G hG hcard
  have hcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_from_drawing K hK hcard hmax
  exact ⟨K, hGK, hK, hcount⟩