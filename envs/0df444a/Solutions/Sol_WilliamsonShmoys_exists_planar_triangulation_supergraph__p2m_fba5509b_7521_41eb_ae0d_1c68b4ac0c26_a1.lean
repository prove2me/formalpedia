-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_fba5509b_7521_41eb_ae0d_1c68b4ac0c26_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:58:41.15389+00:00
-- url     : https://prove2.me/submissions/731cf4e3-f476-4d7e-9935-04783ec76089
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ L : SimpleGraph V,
      H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hHL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
      H hcard hH
  refine ⟨L, hHL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
    L hcard hL hmax