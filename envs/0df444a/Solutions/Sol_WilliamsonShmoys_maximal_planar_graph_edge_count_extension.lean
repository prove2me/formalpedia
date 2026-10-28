-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:36:45.080659+00:00
-- url     : https://prove2.me/submissions/7cce99b1-5bf1-4bcb-9acd-6fff499f01a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_extension_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_extension_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    Exists fun L : SimpleGraph V => K <= L /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hExists :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_extension_exists_maximal_supergraph K hK
  apply Exists.elim hExists
  intro L hL
  refine Exists.intro L ?_
  refine And.intro hL.1 ?_
  refine And.intro hL.2.1 ?_
  exact WilliamsonShmoys.maximal_planar_graph_edge_count_extension_maximal_edge_count
    L hL.2.1 hL.2.2 hV