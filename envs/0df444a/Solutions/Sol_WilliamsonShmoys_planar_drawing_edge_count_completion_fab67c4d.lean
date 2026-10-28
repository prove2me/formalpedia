-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_completion_fab67c4d
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:40:20.117079+00:00
-- url     : https://prove2.me/submissions/b3bca8b2-c163-4403-a2a3-d10306660b9a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices_fddd844c
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_fddd844c

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeSet ⊆ M.edgeSet ∧
      3 * (Fintype.card V : Int) - 6 = (M.edgeSet.ncard : Int) := by
  obtain ⟨M, hM, hLM, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices_fddd844c L hL hCard
  exact ⟨M, hM, hLM,
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing_fddd844c M hM hCard hMax⟩