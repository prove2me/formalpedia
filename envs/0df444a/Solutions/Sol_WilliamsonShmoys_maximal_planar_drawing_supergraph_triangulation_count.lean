-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_supergraph_triangulation_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:47:18.445953+00:00
-- url     : https://prove2.me/submissions/1ad03bb2-bf1a-4e82-ae89-429ba216ce96
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_count_95ea5390
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_95ea5390

set_option autoImplicit false

open WilliamsonShmoys in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    exists_maximal_planar_supergraph_for_edge_count_95ea5390 L hL
  exact ⟨M, hLM, hM,
    edge_count_of_maximal_planar_drawing_95ea5390 M hM hV hmax⟩