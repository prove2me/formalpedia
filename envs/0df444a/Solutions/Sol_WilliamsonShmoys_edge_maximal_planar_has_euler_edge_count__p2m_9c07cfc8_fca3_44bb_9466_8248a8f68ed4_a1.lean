-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_has_euler_edge_count__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:22:25.193791+00:00
-- url     : https://prove2.me/submissions/0776bf23-7847-4ced-ae0d-379918fbfc8c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_edge_count__p2m_24bfc568_7b25_4409_b2ae_c59e72f324da_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNplanar, hEuler⟩ :=
    WilliamsonShmoys.planar_supergraph_with_euler_edge_count__p2m_24bfc568_7b25_4409_b2ae_c59e72f324da_a1
      M hplanar hcard
  have hNM : N ≤ M := hmax N hMN hNplanar
  have hEq : M = N := le_antisymm hMN hNM
  simpa [hEq] using hEuler