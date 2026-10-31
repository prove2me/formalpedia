-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5ab9b52f_fdb8_4eff_9a4e_c2dd12c7a0d0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:53:17.191205+00:00
-- url     : https://prove2.me/submissions/2f18aaf0-f5ae-4785-aaf6-8a232d460a8d

import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_edge_count__p2m_a3a14366_dd9a_40cc_8d47_64e2f5da9564_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hMDraw, hMCount⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_edge_count__p2m_a3a14366_dd9a_40cc_8d47_64e2f5da9564_a1
      L hDraw hV
  have hEq : M = L := hMax M hLM hMDraw
  rw [← hEq]
  exact hMCount