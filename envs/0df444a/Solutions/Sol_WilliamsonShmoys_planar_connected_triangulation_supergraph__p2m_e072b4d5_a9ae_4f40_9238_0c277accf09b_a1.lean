-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_triangulation_supergraph__p2m_e072b4d5_a9ae_4f40_9238_0c277accf09b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:34.478299+00:00
-- url     : https://prove2.me/submissions/477311d0-4850-48bb-a8d7-fbe4c278f6f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1

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
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
      M hM
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
      N hN hMax hCard
  exact ⟨N, hMN, hN, hCount⟩