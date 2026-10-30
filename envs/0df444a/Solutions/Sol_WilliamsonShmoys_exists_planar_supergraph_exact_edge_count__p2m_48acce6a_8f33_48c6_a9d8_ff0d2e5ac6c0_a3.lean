-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_exact_edge_count__p2m_48acce6a_8f33_48c6_a9d8_ff0d2e5ac6c0_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:29:59.928501+00:00
-- url     : https://prove2.me/submissions/ceb4eadd-e2a9-4351-a8c0-6fa695bc3b80

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_9b481115_396e_4251_a44a_4293d6576e9f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_has_exact_edge_count__p2m_9b481115_396e_4251_a44a_4293d6576e9f_a1

set_option autoImplicit false

open SimpleGraph

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, N ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hNM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9b481115_396e_4251_a44a_4293d6576e9f_a1
      N hN
  exact ⟨M, hNM, hM,
    WilliamsonShmoys.maximal_planar_has_exact_edge_count__p2m_9b481115_396e_4251_a44a_4293d6576e9f_a1
      M hM hV hmax⟩