-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:39:23.694595+00:00
-- url     : https://prove2.me/submissions/73290121-391d-4c96-83d3-8b42fd201ab9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        3 * Fintype.card V - 6 = Q.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hQ, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph P hP
  exact ⟨Q, hPQ, hQ,
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing_v2 Q hV hQ hmax⟩