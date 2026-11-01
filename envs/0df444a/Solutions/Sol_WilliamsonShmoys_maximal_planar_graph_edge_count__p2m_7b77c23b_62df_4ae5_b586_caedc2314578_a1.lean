-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_7b77c23b_62df_4ae5_b586_caedc2314578_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:11:30.20623+00:00
-- url     : https://prove2.me/submissions/ee546fca-59e5-4b9c-a604-2c18d8736fe0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
    K hplanar hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_ac7ad3d7_f745_41b8_8bbb_a0b9a0b84694_a1
    K hplanar hcard hmax
  omega