-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_61f827a4_90a1_438d_8856_22a36ff94a2a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:51:28.718086+00:00
-- url     : https://prove2.me/submissions/5a5a1d7a-d055-44e2-8ce2-5b117b8dcb7b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_maximal__p2m_2266ad6e_a873_4db0_8a1d_ced08babaea4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2266ad6e_a873_4db0_8a1d_ced08babaea4_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G.edgeSet ⊆ L.edgeSet ∧
      HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hGL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_2266ad6e_a873_4db0_8a1d_ced08babaea4_a1
      G hplanar
  exact ⟨L, hGL, hL,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_2266ad6e_a873_4db0_8a1d_ced08babaea4_a1
      L hcard hL hmax⟩