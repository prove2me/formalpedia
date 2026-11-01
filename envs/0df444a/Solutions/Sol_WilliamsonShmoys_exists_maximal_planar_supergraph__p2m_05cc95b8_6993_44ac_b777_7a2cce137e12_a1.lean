-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:13.070865+00:00
-- url     : https://prove2.me/submissions/d251cbde-2749-4223-b33d-43f1278d8158

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_max_edge_ncard__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
import Theorems.Thm_WilliamsonShmoys_edge_ncard_mono__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
import Theorems.Thm_WilliamsonShmoys_edge_ncard_eq_reverse_le__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N ≤ M := by
  classical
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_max_edge_ncard__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
      L hL
  refine ⟨M, hLM, hM, ?_⟩
  intro N hMN hN
  have hNleM : N.edgeSet.ncard ≤ M.edgeSet.ncard :=
    hmax N (le_trans hLM hMN) hN
  have hMleN : M.edgeSet.ncard ≤ N.edgeSet.ncard :=
    WilliamsonShmoys.edge_ncard_mono__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
      M N hMN
  have hcard : M.edgeSet.ncard = N.edgeSet.ncard :=
    Nat.le_antisymm hMleN hNleM
  exact
    WilliamsonShmoys.edge_ncard_eq_reverse_le__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
      M N hMN hcard