-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_graph_edge_count__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:26:12.624715+00:00
-- url     : https://prove2.me/submissions/66d6d851-7d02-4eca-ab6e-cd3f62a02e44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_upper_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_graph_edge_upper_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1 K hK hCard
  have hlower := WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1 K hK hCard hmax
  omega