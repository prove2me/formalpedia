-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_with_exact_euler_edge_count_95ea5390
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:26:05.944913+00:00
-- url     : https://prove2.me/submissions/fc8c1117-2e4a-49a4-9cbd-9896be5f1fa3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    exists N : SimpleGraph V,
      M <= N /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1 M hM hV
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_euler_count__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1 N hN hmax hV⟩