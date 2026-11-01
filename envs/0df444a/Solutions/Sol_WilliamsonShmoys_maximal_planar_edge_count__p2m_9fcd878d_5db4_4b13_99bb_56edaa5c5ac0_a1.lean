-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_9fcd878d_5db4_4b13_99bb_56edaa5c5ac0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:45.004815+00:00
-- url     : https://prove2.me/submissions/c4e38ef2-488c-4339-83a8-4e4725603315
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : forall (P : SimpleGraph V),
      (forall u v, G.Adj u v -> P.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn P -> P = G)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V = G.edgeSet.ncard + 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1 G hG hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_0d2111fe_49a0_4983_b8b9_46fbb1acc127_a1 G hG hMax hCard
  omega