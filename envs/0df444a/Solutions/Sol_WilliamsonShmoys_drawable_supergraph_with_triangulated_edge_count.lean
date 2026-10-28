-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_with_triangulated_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:35:53.853889+00:00
-- url     : https://prove2.me/submissions/7860f62c-0a7b-4852-8dda-56af67b0529f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_maximal_exists_b20803f2_ba1d_4792_8629_bbbc0caa0274
import Theorems.Thm_WilliamsonShmoys_edge_maximal_drawing_has_three_n_minus_six_edges_b20803f2_ba1d_4792_8629_bbbc0caa0274

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, J.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hJK, hKDraw, hKMax⟩ :=
    WilliamsonShmoys.drawable_supergraph_edge_maximal_exists_b20803f2_ba1d_4792_8629_bbbc0caa0274
      J hDraw
  refine ⟨K, hJK, hKDraw, ?_⟩
  exact WilliamsonShmoys.edge_maximal_drawing_has_three_n_minus_six_edges_b20803f2_ba1d_4792_8629_bbbc0caa0274
    K hKDraw hKMax hCard