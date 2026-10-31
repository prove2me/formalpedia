-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_triangulation_supergraph__p2m_e072b4d5_a9ae_4f40_9238_0c277accf09b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:33:49.071489+00:00
-- url     : https://prove2.me/submissions/851e7c9c-4cf9-4c4e-8e76-10fdfa28729a

import Theorems.Thm_WilliamsonShmoys_triangulated_supergraph_of_connected_drawing

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hConn : M.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.triangulated_supergraph_of_connected_drawing M hM hConn hCard
