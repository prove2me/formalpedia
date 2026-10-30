-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_cardinality__p2m_e15f7e2c_ce0e_4996_9963_e731b96f551d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:57:18.443683+00:00
-- url     : https://prove2.me/submissions/65a44f84-2aba-4726-8761-6c4bb937d620

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_has_maximal_extension__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ∧
      HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_has_maximal_extension__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
      L hL
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
      M hM hCard hmax
  exact ⟨M, hLM, hM, hcount⟩
