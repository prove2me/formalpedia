-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:36:36.75024+00:00
-- url     : https://prove2.me/submissions/64f4ff47-194a-4b9f-b7f7-4b55406baab6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_triangulation_count_3624186a_b460_4cf9_8afd_86ec1a2d5ee8

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset N.edgeSet K.edgeSet ->
      N.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hInc⟩ :=
    WilliamsonShmoys.maximal_planar_graph_triangulation_count_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
      N hN hmax hV
  omega