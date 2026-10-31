-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_1bca9e8d_9b62_4fe4_94af_9f67da983417_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:33:43.345985+00:00
-- url     : https://prove2.me/submissions/4f70a07e-999c-4738-b381-e2a56f4da0f4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1 M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_6f52b5a3_b090_4468_aa84_13620a15b574_a1 N hN hmax hCard⟩