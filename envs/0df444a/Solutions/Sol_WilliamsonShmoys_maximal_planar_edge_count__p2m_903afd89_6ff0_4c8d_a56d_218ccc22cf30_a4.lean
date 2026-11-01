-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:00:27.210747+00:00
-- url     : https://prove2.me/submissions/141d2c0e-eb38-4853-90a3-3e5a43c9db1d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ Q : SimpleGraph V, N ≤ Q →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hNQ, hQplanar, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count
      N hcard hplanar
  have hQN : Q ≤ N := hmax Q hNQ hQplanar
  have hEq : Q = N := le_antisymm hQN hNQ
  rw [hEq] at hcount
  exact hcount.symm