-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_euler_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:51:16.263609+00:00
-- url     : https://prove2.me/submissions/b8fc47a3-6812-4a49-b458-33090a3f42a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_euler_completion
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_euler_edge_count_for_euler_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      N <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_euler_completion N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.maximal_planar_graph_euler_edge_count_for_euler_completion
      K hV hK hMax⟩