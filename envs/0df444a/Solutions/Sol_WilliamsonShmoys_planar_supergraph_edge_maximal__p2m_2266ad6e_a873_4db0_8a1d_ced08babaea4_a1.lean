-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_2266ad6e_a873_4db0_8a1d_ced08babaea4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:05:51.294479+00:00
-- url     : https://prove2.me/submissions/98eabc3c-df15-4883-b94a-8b66f6487c99

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_edge_maximal_extension__p2m_89ca6453_1971_4f8a_b52b_11a113611db9_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hplanar : HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G.edgeSet ⊆ L.edgeSet ∧
      HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → K.edgeSet = L.edgeSet := by
  exact WilliamsonShmoys.finite_edge_maximal_extension__p2m_89ca6453_1971_4f8a_b52b_11a113611db9_a1
    HasPlanarDrawingOn G hplanar