-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:32.442529+00:00
-- url     : https://prove2.me/submissions/6f566013-330c-4f66-bdec-f36bfde4a90c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper__p2m_a82d4d7c_d6e6_4425_a735_0c3a8fa81594_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_a82d4d7c_d6e6_4425_a735_0c3a8fa81594_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_simple_graph_edge_count_upper__p2m_a82d4d7c_d6e6_4425_a735_0c3a8fa81594_a1 K hcard hK
  · exact WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_a82d4d7c_d6e6_4425_a735_0c3a8fa81594_a1 K hcard hK hmax