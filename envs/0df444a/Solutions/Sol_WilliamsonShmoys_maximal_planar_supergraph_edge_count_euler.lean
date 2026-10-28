-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count_euler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:50:06.903526+00:00
-- url     : https://prove2.me/submissions/6e08300e-0ad4-4da3-b229-e11864f49a04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_euler_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_euler_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U X : SimpleGraph V)
    (hmax : WilliamsonShmoys.IsPlanarMaximalSupergraphForEdgeCountCompletion U X)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  have hdraw : WilliamsonShmoys.HasPlanarDrawingOn X := hmax.1
  have hupper := WilliamsonShmoys.maximal_planar_supergraph_edge_count_euler_upper_bound X hdraw hCard
  have hlower := WilliamsonShmoys.maximal_planar_supergraph_edge_count_euler_lower_bound X hdraw hmax.2.2 hCard
  omega