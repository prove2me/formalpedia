-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:18:06.202802+00:00
-- url     : https://prove2.me/submissions/1cf7f744-db20-466a-8552-88000902f04c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound_for_supergraph_completion

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun L : SimpleGraph V => K <= L /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      3 * Fintype.card V - 6 <= L.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_graph_edge_bound_for_supergraph_completion
      L hV hL hmax⟩